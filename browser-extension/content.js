(() => {
  // 大肥鱼搜题：读取本机答案 → 高亮正确选项 → 自动点选
  //
  // 设计要点：
  // 1. 只点「正确答案」对应的选项，不会去碰提交、下一题之类的按钮；
  // 2. 已选中的选项不重复点（幂等），页面重新渲染后会自动补选；
  // 3. 单选组（radio）只点一个；多选组（checkbox）按答案逐项勾选，
  //    并把该组里明确不属于答案的选项取消掉；
  // 4. 保护：每个选项最多尝试 3 次，10 秒内点击总数有上限，
  //    避免页面反复重置时和页面互相打架；
  // 5. 随时可按 Alt+Shift+P 暂停/恢复自动点选，高亮不受影响；
  // 6. 只有「选项先出现、答案后到达」的题才会点选。如果答案先到、选项后渲染，
  //    本次只高亮不点击（状态栏会提示），等下一批答案再点，避免用旧答案点新题。
  const HIGHLIGHT_CLASS = "dfy-correct-option";
  const SELECTED_CLASS = "dfy-correct-option-selected";
  const STATUS_ID = "dfy-answer-status";
  const INPUT_SELECTOR = 'input[type="radio"], input[type="checkbox"]';
  const MAX_CLICK_TRIES = 3;
  const CLICK_COOLDOWN_MS = 900;
  const RETRY_DELAY_MS = 240;
  const CLICK_BUDGET = 30;
  const CLICK_BUDGET_WINDOW_MS = 10000;
  // 多选点击之间留出间隔，等页面框架把上一题的选择写回状态
  const CLICK_GAP_MS = 200;
  const TOGGLE_KEY_CODE = "KeyP";
  const DUMP_KEY_CODE = "KeyD";

  // 判断题常见写法
  const TRUE_TOKENS = ["对", "正确", "是", "true", "t", "√"];
  const FALSE_TOKENS = ["错", "错误", "否", "false", "f", "×"];

  let lastUpdated = -1;
  let lastData = null;
  let reapplyTimer = null;
  let clickTimer = null;
  let fillRetryTimer = null;
  let requestInFlight = false;
  let autoClickEnabled = true;

  // 已点过的选项：input -> { tries, at }
  let clickState = new WeakMap();
  let clickBudgetUsed = 0;
  let clickBudgetStart = Date.now();

  // 当前这批答案命中的选项，用于刷新状态栏
  let matchedOptions = [];
  let unselected = [];
  let summary = null;

  // 这批答案到达的时间，以及每个选项组第一次出现的时间。
  // 只有「选项先出现、答案后到达」的题才会自动点选；答案先到则本次只高亮。
  let answerBatchAt = 0;
  let activeSections = null;
  let activeSignatures = null;
  let quizCheckAt = 0;
  let quizCheckResult = false;
  let quizChecked = false;
  const groupSeenElements = new WeakMap();
  const groupSeenKeys = new Map();
  const numberCache = new WeakMap();
  const sectionCache = new WeakMap();

  function normalize(text) {
    return String(text || "")
      .normalize("NFKC")
      .replace(/[\s\p{P}\p{S}_]+/gu, "")
      .toLowerCase();
  }

  function setStatus(text, tone) {
    if (window.top !== window) {
      // 顶层确实有题目时才由顶层显示；跨域或顶层只有普通表单时允许当前框架显示
      let topHasQuiz = false;
      try {
        topHasQuiz = documentHasQuiz(window.top.document);
      } catch (_) {
        topHasQuiz = false;
      }
      if (topHasQuiz) {
        return;
      }
    }
    // 所有网站都会注入，非答题页面不显示悬浮条
    if (!pageHasQuiz()) {
      return;
    }
    let node = document.getElementById(STATUS_ID);
    if (!node) {
      node = document.createElement("div");
      node.id = STATUS_ID;
      node.title = "Alt+Shift+P 暂停/恢复自动选择";
      (document.body || document.documentElement).appendChild(node);
    }
    node.textContent = text;
    node.dataset.tone = tone || "ok";
  }

  // 只认“带题号的题目/选项”，避免普通页面的搜索框、筛选复选框把状态条引出来
  function documentHasQuiz(doc) {
    if (!doc) {
      return false;
    }
    if (doc.querySelector(CHAOXING_QUESTION_SELECTOR)) {
      return true;
    }
    let checked = 0;
    for (const input of doc.querySelectorAll(INPUT_SELECTOR)) {
      checked += 1;
      if (checked > 20) {
        break;
      }
      if (findQuestionNumber(input.parentElement || input)) {
        return true;
      }
    }
    return false;
  }

  function isVisible(el) {
    if (!el || !el.isConnected) {
      return false;
    }
    const rect = el.getBoundingClientRect();
    if (rect.width <= 0 || rect.height <= 0) {
      return false;
    }
    const style = window.getComputedStyle(el);
    if (style.display === "none" || style.visibility === "hidden") {
      return false;
    }
    return parseFloat(style.opacity || "1") !== 0;
  }

  // 选项组是否在当前视口里（同号题分布在多个大题时用来挑正确的那个）
  function isRecordOnScreen(record) {
    for (const input of record.inputs) {
      const element = labelFor(input) || input;
      if (!element || !element.isConnected) {
        continue;
      }
      const rect = element.getBoundingClientRect();
      if (rect.width <= 0 || rect.height <= 0) {
        continue;
      }
      if (rect.bottom > 0 && rect.top < window.innerHeight) {
        return true;
      }
    }
    return false;
  }

  function isDisabled(input) {
    if (!input) {
      return true;
    }
    if (input.disabled) {
      return true;
    }
    try {
      if (input.matches && input.matches(":disabled")) {
        return true;
      }
    } catch (_) {
      /* 忽略 */
    }
    return !!(input.closest && input.closest('[aria-disabled="true"]'));
  }

  function clearHighlights() {
    document
      .querySelectorAll("." + HIGHLIGHT_CLASS + ", ." + SELECTED_CLASS)
      .forEach((node) => {
        node.classList.remove(HIGHLIGHT_CLASS, SELECTED_CLASS);
      });
  }

  function labelFor(input) {
    const label = input.closest("label");
    if (label) {
      return label;
    }
    if (input.id && window.CSS && CSS.escape) {
      const explicit = document.querySelector(`label[for="${CSS.escape(input.id)}"]`);
      if (explicit) {
        return explicit;
      }
    }
    return input.parentElement;
  }

  function groupFor(input) {
    let node = input.parentElement;
    for (let depth = 0; depth < 8 && node; depth += 1, node = node.parentElement) {
      if (node.querySelectorAll(INPUT_SELECTOR).length >= 2) {
        return node;
      }
    }
    return input.parentElement;
  }

  function findQuestionNumber(group) {
    let node = group;
    for (let depth = 0; depth < 7 && node; depth += 1, node = node.parentElement) {
      const text = node.innerText || "";
      let match = text.match(/(?:^|\n)\s*(\d{1,3})\s*[.．、]/);
      if (match) {
        return match[1];
      }
      match = text.match(/第\s*(\d{1,3})\s*题/);
      if (match) {
        return match[1];
      }
    }
    return "";
  }

  // innerText 会触发布局，这里按选项组缓存题号
  function questionNumberFor(group) {
    if (numberCache.has(group)) {
      return numberCache.get(group);
    }
    const number = findQuestionNumber(group);
    if (number) {
      numberCache.set(group, number);
    }
    return number;
  }

  const SECTION_KINDS = ["是非题", "判断题", "单选题", "多选题", "填空题"];

  function kindInText(text) {
    const kinds = SECTION_KINDS.filter((kind) => text.includes(kind));
    return kinds.length === 1 ? kinds[0] : "";
  }

  // 找到选项组所属的大题标题（是非题 / 单选题 / 多选题 / 填空题）
  function sectionKeyFor(group) {
    if (sectionCache.has(group)) {
      return sectionCache.get(group);
    }
    let key = "";
    let node = group;
    for (let depth = 0; depth < 10 && node && node !== document.body; depth += 1, node = node.parentElement) {
      const text = node.innerText || "";
      const kinds = SECTION_KINDS.filter((kind) => text.includes(kind));
      if (kinds.length === 1) {
        key = kinds[0];
        break;
      }
      if (kinds.length > 1) {
        break;
      }
    }
    // 题目标题和题目平铺在同一个容器里时，往前面的兄弟节点找标题
    if (!key) {
      let cursor = group;
      for (let depth = 0; depth < 8 && cursor; depth += 1, cursor = cursor.parentElement) {
        let prev = cursor.previousElementSibling;
        for (let i = 0; i < 6 && prev; i += 1, prev = prev.previousElementSibling) {
          const found = kindInText(prev.innerText || "");
          if (found) {
            key = found;
            break;
          }
        }
        if (key) {
          break;
        }
      }
    }
    if (key) {
      sectionCache.set(group, key);
    }
    return key;
  }

  // 这批答案到达时，屏幕上正在显示哪些大题；之后重绘/滚动都只处理这些大题
  function visibleSectionKeys() {
    const keys = new Set();
    for (const [group, inputs] of collectGroups()) {
      if (!isRecordOnScreen({ inputs })) {
        continue;
      }
      const key = sectionKeyFor(group);
      if (key) {
        keys.add(key);
      }
    }
    for (const item of collectFillInputs()) {
      if (!isElementOnScreen(item.element)) {
        continue;
      }
      if (item.section) {
        keys.add(item.section);
      }
    }
    return keys;
  }

  // 这批答案到达时，屏幕上具体是哪几道题（题号 + 选项文字指纹）。
  // 之后不管页面怎么滚动/重绘，都只点这几道题，绝不回头改屏幕外的题。
  function visibleGroupSignatures() {
    const set = new Set();
    for (const [group, inputs] of collectGroups()) {
      if (!isRecordOnScreen({ inputs })) {
        continue;
      }
      set.add(groupFingerprint(group, inputs));
    }
    return set;
  }

  // 选项字母：先看「A.」「A、」这类前缀，再看 value，最后按顺序推
  function optionLetter(label, input, index) {
    const text = (label.innerText || "").trim();
    const match = text.match(/^\s*([A-Da-d])\s*[.．、:：)）]?\s*/);
    if (match) {
      return match[1].toUpperCase();
    }
    const value = String(input.value || "").trim();
    if (/^[A-Da-d]$/.test(value)) {
      return value.toUpperCase();
    }
    return String.fromCharCode(65 + index);
  }

  // 只认页面上明确写出来的字母，用于「取消错误勾选」这种需要确定性的场景
  function explicitOptionLetter(label, input) {
    const text = (label.innerText || "").trim();
    const match = text.match(/^\s*([A-Da-d])\s*[.．、:：)）]?\s*/);
    if (match) {
      return match[1].toUpperCase();
    }
    const value = String(input.value || "").trim();
    if (/^[A-Da-d]$/.test(value)) {
      return value.toUpperCase();
    }
    return "";
  }

  function collectGroups() {
    const inputs = Array.from(document.querySelectorAll(INPUT_SELECTOR));
    const groups = new Map();
    for (const input of inputs) {
      const group = groupFor(input);
      if (!group) {
        continue;
      }
      if (!groups.has(group)) {
        groups.set(group, []);
      }
      groups.get(group).push(input);
    }
    return groups;
  }

  const FILLABLE_SELECTOR = 'input, textarea, [contenteditable="true"]';

  function isFillable(element) {
    if (!element || element.disabled || element.readOnly) {
      return false;
    }
    if (element.isContentEditable) {
      return true;
    }
    if (element.tagName === "TEXTAREA") {
      return true;
    }
    if (element.tagName === "INPUT") {
      const type = String(element.type || "text").toLowerCase();
      return type === "text" || type === "search" || type === "number" || type === "tel";
    }
    return false;
  }

  function isElementOnScreen(element) {
    if (!element || !element.isConnected) {
      return false;
    }
    const rect = element.getBoundingClientRect();
    return rect.width > 0 && rect.height > 0 && rect.bottom > 0 && rect.top < window.innerHeight;
  }

  function elementValue(element) {
    return element.isContentEditable ? String(element.textContent || "") : String(element.value || "");
  }

  // 填空题：按题号找到对应输入框（支持 input / textarea / contenteditable）
  function collectFillInputs() {
    const list = [];
    for (const element of document.querySelectorAll(FILLABLE_SELECTOR)) {
      if (!isFillable(element) || !isVisible(element)) {
        continue;
      }
      const number = findQuestionNumber(element.parentElement || element);
      if (!number) {
        continue;
      }
      list.push({
        element,
        number,
        section: sectionKeyFor(element.parentElement || element),
      });
    }
    return list;
  }

  function setFillValue(element, value) {
    if (element.isContentEditable) {
      element.textContent = value;
    } else {
      const proto = element.tagName === "TEXTAREA" ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
      const descriptor = Object.getOwnPropertyDescriptor(proto, "value");
      if (descriptor && descriptor.set) {
        descriptor.set.call(element, value);
      } else {
        element.value = value;
      }
    }
    element.dispatchEvent(new Event("input", { bubbles: true }));
    element.dispatchEvent(new Event("change", { bubbles: true }));
  }

  // 一个题有多个空时，按「；/、/|」拆分答案；拆不出来就只填第一个空
  function splitFillAnswer(answer, count) {
    const parts = String(answer || "")
      .split(/[;；|、\n]+/)
      .map((part) => part.trim())
      .filter(Boolean);
    return count > 1 && parts.length === count ? parts : null;
  }

  // 页面像不像答题页：有单选/复选框，或有带题号的文本输入框。
  // 所有网站都会注入，用它避免在普通网页上显示悬浮状态条。
  function pageHasQuiz() {
    const now = performance.now();
    if (quizChecked && now - quizCheckAt < 5000) {
      return quizCheckResult;
    }
    quizChecked = true;
    quizCheckAt = now;
    quizCheckResult = false;
    if (document.querySelector(CHAOXING_QUESTION_SELECTOR)) {
      quizCheckResult = true;
      return quizCheckResult;
    }
    // 只有“带题号”的单选/复选框才算题目；普通页面的筛选框、搜索框、章节列表不算
    let checked = 0;
    for (const [group] of collectGroups()) {
      checked += 1;
      if (checked > 30) {
        break;
      }
      if (questionNumberFor(group)) {
        quizCheckResult = true;
        return quizCheckResult;
      }
    }
    return quizCheckResult;
  }

  const CHAOXING_QUESTION_SELECTOR = ".TiMu";

  // 超星/学习通“作业、测验”页面：选项是 li + span[data]，没有原生 radio/checkbox
  function collectChaoxingQuestions() {
    const list = [];
    for (const element of document.querySelectorAll(CHAOXING_QUESTION_SELECTOR)) {
      const title = element.querySelector(".Zy_TItle i.fl");
      const number = title ? String(title.textContent || "").replace(/\D/g, "") : "";
      if (!number) {
        continue;
      }
      const options = Array.from(element.querySelectorAll("ul.Zy_ulTop li")).map((li) => {
        const span = li.querySelector("[data]");
        const data = span ? String(span.getAttribute("data") || "") : "";
        const spanText = String((span && span.textContent) || "").trim().toUpperCase();
        const ariaLabel = String(li.getAttribute("aria-label") || "").trim().toUpperCase();
        const letter = /^[A-Z]$/.test(spanText)
          ? spanText
          : /^[A-Z]$/.test(ariaLabel.slice(0, 1))
            ? ariaLabel.slice(0, 1)
            : "";
        const textNode = li.querySelector("a.after") || span;
        const text = String((textNode && textNode.textContent) || "").trim();
        const selected = !!(
          span &&
          (span.classList.contains("check_answer") || span.classList.contains("check_answer_dx"))
        );
        return { li, span, data, letter, text, selected };
      });
      const blanks = Array.from(element.querySelectorAll(".blankItemDiv")).map((div, index) => ({
        index,
        iframe: div.querySelector(".textDIV iframe"),
        textarea: div.querySelector("textarea"),
        inpDiv: div.querySelector(".InpDIV"),
      }));
      if (!options.length && !blanks.length) {
        continue;
      }
      const rawType = element.getAttribute("data");
      let type = rawType === null ? -1 : Number(rawType);
      if (!Number.isFinite(type) || type < 0) {
        if (options.some((option) => /^(true|false)$/i.test(String(option.data)))) {
          type = 3;
        } else if (element.querySelector(".num_option_dx")) {
          type = 1;
        } else if (blanks.length) {
          type = 2;
        } else {
          type = 0;
        }
      }
      list.push({ element, number, type, options, blanks });
    }
    return list;
  }

  function chaoxingWantedData(question, answer) {
    const letters = parseLetters(answer);
    if (question.type === 3) {
      const kind = trueFalseKind(answer);
      if (kind) {
        return [kind];
      }
      if (letters.length === 1) {
        return [letters[0] === "A" ? "true" : "false"];
      }
      return [];
    }
    if (letters.length) {
      return letters;
    }
    const parts = String(answer)
      .split(/[;；|]/)
      .map((part) => normalize(part))
      .filter(Boolean);
    const wanted = [];
    for (const option of question.options) {
      const optionNorm = normalize(option.text);
      if (!optionNorm) {
        continue;
      }
      if (parts.some((part) => part.includes(optionNorm) || optionNorm.includes(part))) {
        wanted.push(option.data);
        if (option.letter) {
          wanted.push(option.letter);
        }
      }
    }
    return wanted;
  }

  // 选项匹配：答案里的字母可能对应页面显示字母（随机选项时 data 可能不同），
  // 判断题还要认“对/错/true/false”。
  function chaoxingOptionMatches(option, wanted) {
    const keys = [String(option.data || "").toUpperCase(), String(option.letter || "").toUpperCase()];
    if (keys.some((key) => key && wanted.has(key))) {
      return true;
    }
    if (wanted.has("TRUE") && /^(对|正确|是|true|√)/i.test(option.text)) {
      return true;
    }
    if (wanted.has("FALSE") && /^(错|错误|否|false|×)/i.test(option.text)) {
      return true;
    }
    return false;
  }

  // UEditor 在页面自己的 JS 里，内容脚本不能直接调 UE；
  // 注入一小段页面脚本，用事件转交内容，再走 DOM 兜底。
  function ensureChaoxingBridge() {
    if (window.__dfyFillBridge) {
      return;
    }
    window.__dfyFillBridge = true;
    try {
      const script = document.createElement("script");
      script.textContent =
        "(function(){if(window.__dfyFillBridgeInstalled){return;}" +
        "window.__dfyFillBridgeInstalled=true;" +
        "document.addEventListener('dfy-fill',function(event){var detail=event.detail||{};" +
        "try{if(window.UE&&UE.getEditor&&detail.id){" +
        "var editor=UE.getEditor(detail.id);" +
        "editor.setContent(detail.text||'');" +
        "if(editor.sync){editor.sync();}" +
        "}}catch(e){}});})();";
      (document.head || document.documentElement).appendChild(script);
      script.remove();
    } catch (_) {
      /* 被 CSP 拦截时忽略，走 DOM 兜底 */
    }
  }

  function fillChaoxingBlank(blank, value) {
    if (blank.textarea && blank.textarea.id) {
      ensureChaoxingBridge();
      try {
        document.dispatchEvent(
          new CustomEvent("dfy-fill", { detail: { id: blank.textarea.id, text: value } })
        );
      } catch (_) {
        /* 忽略 */
      }
    }
    const doc = blank.iframe && blank.iframe.contentDocument;
    if (doc && doc.body) {
      doc.body.textContent = value;
      doc.body.dispatchEvent(new Event("input", { bubbles: true }));
    }
    if (blank.textarea) {
      const descriptor = Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype, "value");
      if (descriptor && descriptor.set) {
        descriptor.set.call(blank.textarea, value);
      } else {
        blank.textarea.value = value;
      }
      blank.textarea.dispatchEvent(new Event("input", { bubbles: true }));
      blank.textarea.dispatchEvent(new Event("change", { bubbles: true }));
    }
    if (blank.inpDiv) {
      blank.inpDiv.textContent = value;
    }
  }

  function fillChaoxingBlanks(question, answer) {
    const blanks = question.blanks;
    if (!blanks.length) {
      return 0;
    }
    const parts = splitFillAnswer(answer, blanks.length);
    let filled = 0;
    blanks.forEach((blank, index) => {
      const value = parts ? parts[index] : index === 0 ? answer : "";
      if (!value) {
        return;
      }
      fillChaoxingBlank(blank, value);
      filled += 1;
    });
    return filled;
  }

  function applyChaoxing(answers) {
    const result = { questions: 0, picked: 0, filled: 0 };
    const questions = collectChaoxingQuestions();
    if (!questions.length) {
      return result;
    }
    for (const question of questions) {
      // 超星题号是连续的（1..N），不存在同号跨大题的问题，整页按题号处理
      if (!answers.has(question.number)) {
        continue;
      }
      const answer = String(answers.get(question.number) || "").trim();
      if (!answer) {
        continue;
      }
      result.questions += 1;
      if (question.type === 2) {
        result.filled += fillChaoxingBlanks(question, answer);
        continue;
      }
      const wanted = new Set(
        chaoxingWantedData(question, answer).map((value) => String(value).toUpperCase())
      );
      if (!wanted.size) {
        continue;
      }
      if (question.type === 1) {
        for (const option of question.options) {
          const shouldPick = chaoxingOptionMatches(option, wanted);
          if (shouldPick && !option.selected) {
            option.li.click();
          } else if (!shouldPick && option.selected) {
            option.li.click();
          }
        }
        // 按“当前实际选中的目标选项数”统计，重复应用时不会变成 0
        for (const option of question.options) {
          if (!chaoxingOptionMatches(option, wanted)) {
            continue;
          }
          const span = option.li.querySelector("[data]");
          if (span && span.classList.contains("check_answer_dx")) {
            result.picked += 1;
          }
        }
      } else {
        const target = question.options.find((option) => chaoxingOptionMatches(option, wanted));
        if (target) {
          if (!target.selected) {
            target.li.click();
          }
          const span = target.li.querySelector("[data]");
          if (span && span.classList.contains("check_answer")) {
            result.picked += 1;
          }
        }
      }
    }
    return result;
  }

  // 用「题号 + 选项文字」做指纹：页面把同一组选项整个重新渲染时，
  // 指纹不变，可以继承第一次出现的时间，避免重绘后突然不再点选。
  function groupFingerprint(group, inputs) {
    const number = questionNumberFor(group) || "?";
    const texts = inputs.map((input) => {
      const label = labelFor(input);
      return normalize((label && label.textContent) || input.value || "");
    });
    return number + "|" + texts.join("|");
  }

  // 记录每个选项组第一次出现在页面上的时间
  function noteGroups() {
    const now = performance.now();
    for (const [group, inputs] of collectGroups()) {
      const key = groupFingerprint(group, inputs);
      const inherited = groupSeenKeys.get(key);
      const known = groupSeenElements.get(group);
      if (known !== undefined) {
        if (inherited === undefined || known < inherited) {
          groupSeenKeys.set(key, known);
        }
        continue;
      }
      const seenAt = inherited === undefined ? now : Math.min(inherited, now);
      groupSeenElements.set(group, seenAt);
      groupSeenKeys.set(key, inherited === undefined ? now : seenAt);
    }
  }

  // 新选项组插入 DOM 时才需要重新记录时间
  function mutationAddsInputs(mutations) {
    for (const mutation of mutations) {
      if (mutation.type !== "childList") {
        continue;
      }
      for (const node of mutation.addedNodes) {
        if (node.nodeType !== 1) {
          continue;
        }
        if (
          (node.matches && node.matches(INPUT_SELECTOR)) ||
          (node.querySelector && node.querySelector(INPUT_SELECTOR))
        ) {
          return true;
        }
      }
    }
    return false;
  }

  // 「A」「A、B」「A；C」「ABC」都能解析
  function parseLetters(answer) {
    const compact = String(answer || "").replace(/[\s、,，;；/／|｜+＋和及与]/g, "");
    if (!/^[A-Da-d]{1,4}$/.test(compact)) {
      return [];
    }
    return compact.toUpperCase().split("");
  }

  function trueFalseKind(answer) {
    const text = String(answer || "")
      .replace(/[\s.．、,，:：;；()（）【】\[\]]/g, "")
      .toLowerCase();
    if (!text || text.length > 6) {
      return "";
    }
    if (TRUE_TOKENS.some((token) => token.toLowerCase() === text)) {
      return "true";
    }
    if (FALSE_TOKENS.some((token) => token.toLowerCase() === text)) {
      return "false";
    }
    return "";
  }

  // 去掉选项字母前缀：「A. 对」→「对」，「A 对」→「对」，「A对」→「对」
  function stripOptionPrefix(text) {
    return String(text || "")
      .replace(/^\s*[A-Za-z]\s*(?:[.．、:：)）]\s*|\s+)/, "")
      .replace(/^\s*[A-Za-z](?=[\u4e00-\u9fff√×])/, "")
      .trim();
  }

  // 选项内容归一化后是否正好是「对/错」这类判断题词
  function booleanOptionText(label, input) {
    return stripOptionPrefix((label && (label.innerText || label.textContent)) || input.value || "")
      .replace(/[\s.．、,，:：;；()（）【】\[\]]/g, "")
      .toLowerCase();
  }

  const BOOLEAN_TOKENS = TRUE_TOKENS.concat(FALSE_TOKENS).map((token) => token.toLowerCase());

  function isBooleanGroup(inputs) {
    if (inputs.length < 2) {
      return false;
    }
    return inputs.every((input) => {
      const label = labelFor(input);
      return !!label && BOOLEAN_TOKENS.includes(booleanOptionText(label, input));
    });
  }

  function matchTrueFalse(labelText, wantTrue) {
    const text = stripOptionPrefix(labelText)
      .replace(/[\s.．、,，:：;；()（）【】\[\]]/g, "")
      .toLowerCase();
    if (!text) {
      return false;
    }
    const tokens = wantTrue ? TRUE_TOKENS : FALSE_TOKENS;
    return tokens.some((token) => {
      const value = token.toLowerCase();
      if (text === value) {
        return true;
      }
      // 「对的」「错误。」这类，允许后面多一两个字
      return text.startsWith(value) && text.length <= value.length + 2;
    });
  }

  // 文字答案匹配：去掉选项字母前缀后再比，多选答案按「；」拆开逐个比
  function matchTextAnswer(labelText, answerNorm, answerParts) {
    const labelNorm = normalize(stripOptionPrefix(labelText));
    if (!labelNorm) {
      return false;
    }
    const parts = answerParts && answerParts.length ? answerParts : [answerNorm];
    return parts.some(
      (part) => !!part && (part.includes(labelNorm) || labelNorm.includes(part))
    );
  }

  // 模拟一次尽量接近真实的鼠标点击：先 pointer/mouse 事件，再触发默认行为
  function fireClickEvents(el) {
    const base = { bubbles: true, cancelable: true, view: window, button: 0 };
    const dispatch = (type, extra) => {
      try {
        const event =
          typeof PointerEvent === "function" && type.startsWith("pointer")
            ? new PointerEvent(type, Object.assign({}, base, extra, {
                pointerId: 1,
                isPrimary: true,
                pointerType: "mouse",
              }))
            : new MouseEvent(type, Object.assign({}, base, extra));
        el.dispatchEvent(event);
      } catch (_) {
        /* 老内核忽略 */
      }
    };
    dispatch("pointerdown", { buttons: 1 });
    dispatch("mousedown", { buttons: 1 });
    dispatch("pointerup", {});
    dispatch("mouseup", {});
    try {
      el.click();
    } catch (_) {
      dispatch("click", {});
    }
  }

  function clickTargetsFor(input, label) {
    const targets = [];
    const add = (el) => {
      if (!el || !el.isConnected || targets.includes(el)) {
        return;
      }
      if (el === input && isDisabled(input)) {
        return;
      }
      targets.push(el);
    };
    if (isVisible(input)) {
      add(input);
      add(label);
    } else {
      // 隐藏的 input（自定义样式很常见）：优先点可见的 label/外层
      add(label);
      add(
        (() => {
          let node = input.parentElement;
          for (let depth = 0; depth < 4 && node; depth += 1, node = node.parentElement) {
            if (node === document.body || node === document.documentElement) {
              return null;
            }
            if (isVisible(node)) {
              return node;
            }
          }
          return null;
        })()
      );
      add(input);
    }
    return targets;
  }

  function consumeClickBudget() {
    const now = Date.now();
    if (now - clickBudgetStart > CLICK_BUDGET_WINDOW_MS) {
      clickBudgetStart = now;
      clickBudgetUsed = 0;
    }
    if (clickBudgetUsed >= CLICK_BUDGET) {
      if (autoClickEnabled) {
        autoClickEnabled = false;
        setStatus("大肥鱼：自动选择已停用（页面在反复重置选项，可按 Alt+Shift+P 恢复）", "warn");
      }
      return false;
    }
    clickBudgetUsed += 1;
    return true;
  }

  // 把某个选项逐步点成期望状态（selected: true 选中 / false 取消）
  function applyOptionState(input, label, selected) {
    if (!autoClickEnabled || !input || !input.isConnected || isDisabled(input)) {
      return;
    }
    if (!!input.checked === !!selected) {
      return;
    }
    const now = Date.now();
    const previous = clickState.get(input);
    if (previous && (previous.tries >= MAX_CLICK_TRIES || now - previous.at < CLICK_COOLDOWN_MS)) {
      return;
    }
    if (!consumeClickBudget()) {
      return;
    }
    const tries = (previous ? previous.tries : 0) + 1;
    clickState.set(input, { tries, at: now });

    const targets = clickTargetsFor(input, label);
    if (!targets.length) {
      return;
    }
    // 每次重试换一个目标，提高对自定义组件的命中率
    const offset = (tries - 1) % targets.length;
    const ordered = targets.slice(offset).concat(targets.slice(0, offset));

    const step = (position) => {
      if (
        !autoClickEnabled ||
        !input.isConnected ||
        isDisabled(input) ||
        !!input.checked === !!selected ||
        position >= ordered.length
      ) {
        return;
      }
      fireClickEvents(ordered[position]);
      if (!!input.checked !== !!selected && position + 1 < ordered.length) {
        setTimeout(() => step(position + 1), RETRY_DELAY_MS);
      }
    };
    step(0);
  }

  function pickPrimaryHit(hits, letters) {
    if (!letters.length) {
      return hits[0];
    }
    const ranked = hits.slice().sort((a, b) => {
      const indexA = letters.indexOf(a.letter);
      const indexB = letters.indexOf(b.letter);
      if (indexA === indexB) {
        return 0;
      }
      if (indexA === -1) {
        return 1;
      }
      if (indexB === -1) {
        return -1;
      }
      return indexA - indexB;
    });
    return ranked[0];
  }

  function renderStatus() {
    if (
      !summary ||
      (!summary.highlighted && !summary.filled && !summary.cxPicked && !summary.cxFilled)
    ) {
      return;
    }
    const {
      questions,
      highlighted,
      conflicts,
      stale,
      offscreen,
      ambiguous,
      filled,
      cxPicked,
      cxFilled,
    } = summary;
    let chosen = 0;
    let total = 0;
    for (const hit of matchedOptions) {
      if (!hit.input.isConnected) {
        continue;
      }
      total += 1;
      if (hit.input.checked) {
        chosen += 1;
        hit.label.classList.add(SELECTED_CLASS);
      } else {
        hit.label.classList.remove(SELECTED_CLASS);
      }
    }
    let text;
    if (!highlighted && !filled && (cxPicked || cxFilled)) {
      text = `大肥鱼：超星页面已选 ${cxPicked} 个选项`;
      if (cxFilled) {
        text += ` · 填空 ${cxFilled} 处`;
      }
    } else if (!highlighted && filled && !cxPicked && !cxFilled) {
      text = `大肥鱼：已填 ${filled} 处空`;
    } else {
      text = `大肥鱼：高亮 ${questions} 题 / ${highlighted} 个选项`;
      if (filled) {
        text += ` · 填空 ${filled} 处`;
      }
      if (cxPicked) {
        text += ` · 超星页已选 ${cxPicked} 个`;
      }
      if (cxFilled) {
        text += ` · 超星页填空 ${cxFilled} 处`;
      }
    }
    if (stale) {
      text += ` · ${stale} 题答案早于选项，本次未点选`;
    }
    if (offscreen) {
      text += ` · ${offscreen} 题不在屏幕内，只高亮`;
    }
    if (ambiguous) {
      text += ` · ${ambiguous} 题同号同屏且题型不同，只高亮`;
    }
    if (autoClickEnabled) {
      text += total ? ` · 已点选 ${chosen}/${total}` : "";
    } else {
      text += " · 自动选择已暂停（Alt+Shift+P 恢复）";
    }
    if (conflicts) {
      text += ` · ${conflicts} 题单选组出现多个答案，只点了第一个`;
    }
    const version = extensionVersion();
    if (version) {
      text += ` · v${version}`;
    }
    setStatus(text, autoClickEnabled ? "ok" : "warn");
  }

  function sampleList(values, limit) {
    const max = limit || 4;
    const head = values.slice(0, max).join("、");
    return values.length > max ? `${head}…` : head;
  }

  // 没匹配上时给出可读的原因，方便直接在状态栏里看出问题
  function describeNoMatch(inputCount, pageNumbers, answerEntries) {
    if (!inputCount) {
      return "页面里没有找到单选/多选框";
    }
    if (!pageNumbers.length) {
      return `找到 ${inputCount} 个选项，但识别不到题号`;
    }
    const answerNumbers = answerEntries.map(([number]) => number);
    if (!pageNumbers.some((number) => answerNumbers.includes(number))) {
      return `题号对不上（页面 ${sampleList(pageNumbers)}；答案 ${sampleList(answerNumbers)}）`;
    }
    return `题号对上了，选项没匹配（答案 ${sampleList(answerEntries.map(([, value]) => value))}）`;
  }

  function extensionVersion() {
    try {
      return chrome.runtime.getManifest().version;
    } catch (_) {
      return "";
    }
  }

  // 逐个点、中间留间隔：页面框架通常要等下一个 tick 才把上一项写回状态，
  // 连续快速点击会互相覆盖，最后只剩一个勾选（多选变单选）。
  function startClickJobs() {
    clearTimeout(clickTimer);
    clickTimer = null;
    if (!autoClickEnabled) {
      return;
    }
    const jobs = [];
    for (const hit of matchedOptions) {
      if (!hit.input.isConnected || isDisabled(hit.input) || hit.input.checked) {
        continue;
      }
      jobs.push({ input: hit.input, label: hit.label, selected: true });
    }    for (const hit of unselected) {
      if (!hit.input.isConnected || isDisabled(hit.input) || !hit.input.checked) {
        continue;
      }
      jobs.push({ input: hit.input, label: hit.label, selected: false });
    }
    if (!jobs.length) {
      renderStatus();
      return;
    }
    const runNext = () => {
      clickTimer = null;
      if (!autoClickEnabled || !jobs.length) {
        renderStatus();
        return;
      }
      const job = jobs.shift();
      if (job.input.isConnected && !isDisabled(job.input)) {
        applyOptionState(job.input, job.label, job.selected);
        renderStatus();
      }
      clickTimer = setTimeout(runNext, CLICK_GAP_MS);
    };
    runNext();
  }

  function collectDiagnostics() {
    const groups = [];
    for (const [group, inputs] of collectGroups()) {
      if (groups.length >= 30) {
        break;
      }
      groups.push({
        number: questionNumberFor(group),
        tag: group.tagName,
        cls: String(group.className || "").slice(0, 100),
        options: inputs.slice(0, 8).map((input, index) => {
          const label = labelFor(input);
          const box = label || input;
          const rect = box.getBoundingClientRect();
          return {
            letter: optionLetter(label || input, input, index),
            type: input.type,
            name: input.name,
            value: input.value,
            checked: !!input.checked,
            visible: isVisible(input),
            labelText: ((label && label.innerText) || "").trim().slice(0, 80),
            labelClass: label ? String(label.className || "").slice(0, 100) : "",
            inputClass: String(input.className || "").slice(0, 100),
            disabled: isDisabled(input),
            rect: [
              Math.round(rect.x),
              Math.round(rect.y),
              Math.round(rect.width),
              Math.round(rect.height),
            ],
          };
        }),
      });
    }
    return {
      version: extensionVersion(),
      url: location.href,
      top: window.top === window,
      answers: lastData ? lastData.answers : null,
      groups,
    };
  }

  function copyText(text) {
    if (navigator.clipboard && navigator.clipboard.writeText) {
      return navigator.clipboard.writeText(text).then(
        () => true,
        () => false
      );
    }
    return Promise.resolve(false);
  }

  function showDump(text) {
    let box = document.getElementById("dfy-dump");
    if (!box) {
      box = document.createElement("textarea");
      box.id = "dfy-dump";
      box.readOnly = true;
      box.style.cssText =
        "position:fixed;left:10px;top:10px;width:520px;height:320px;z-index:2147483647;" +
        "font:11px/1.4 monospace;background:#111;color:#eee;padding:8px;border-radius:6px;" +
        "white-space:pre;";
      (document.body || document.documentElement).appendChild(box);
    }
    box.value = text;
    box.focus();
    box.select();
  }


  function applyAnswers(data) {
    clearHighlights();
    matchedOptions = [];
    unselected = [];
    summary = null;
    // 先把当前页面上的选项组都打上出现时间，再判断哪些组是在答案之后才出现的
    noteGroups();

    const answers = new Map();
    for (const item of (data && data.answers) || []) {
      const number = String(item.number || "").trim();
      const answer = String(item.answer || "").trim();
      if (number && answer) {
        answers.set(number, answer);
      }
    }
    if (!answers.size) {
      setStatus("大肥鱼：还没有答案", "ok");
      return;
    }

    let matchedQuestions = 0;
    let highlighted = 0;
    let conflicts = 0;
    let staleQuestions = 0;
    let offscreenQuestions = 0;
    let ambiguousQuestions = 0;

    const records = [];
    for (const [group, inputs] of collectGroups()) {
      records.push({
        group,
        inputs,
        number: questionNumberFor(group),
        section: sectionKeyFor(group),
        signature: groupFingerprint(group, inputs),
        isBoolean: isBooleanGroup(inputs),
        isCheckbox: inputs.some((input) => input.type === "checkbox"),
      });
    }
    const groupsByNumber = new Map();
    for (const record of records) {
      if (!record.number || !answers.has(record.number)) {
        continue;
      }
      // 只处理答案到达时屏幕上的那几道题，屏幕外的题绝不点
      if (
        activeSignatures &&
        activeSignatures.size &&
        !activeSignatures.has(record.signature)
      ) {
        continue;
      }
      // 这批答案只属于答案到达时屏幕上的那几个大题，
      // 之后滚到别的大题也不会再去点它。
      if (
        activeSections &&
        activeSections.size &&
        record.section &&
        !activeSections.has(record.section)
      ) {
        continue;
      }
      if (!groupsByNumber.has(record.number)) {
        groupsByNumber.set(record.number, []);
      }
      groupsByNumber.get(record.number).push(record);
    }

    for (const [number, siblings] of groupsByNumber) {
      const answer = answers.get(number);
      const letters = parseLetters(answer);
      const trueFalse = trueFalseKind(answer);
      const answerNorm = normalize(answer);
      const answerParts =
        !letters.length && !trueFalse
          ? String(answer)
              .split(/[;；|]/)
              .map((part) => normalize(part))
              .filter(Boolean)
          : [];
      if (!letters.length && !trueFalse && !answerNorm) {
        continue;
      }

      // 每个大题都会从 1 重新编号，同一个题号在页面上可能出现多次。
      // 判断题答案只落到「对/错」选项组；多字母答案只落到复选框组；
      // 单字母/文字答案可能是判断题写成 A/B，也可能是单选题，
      // 交给「当前屏幕可见的那一组」决定，屏幕外的题只高亮、不点选。
      const plainGroups = siblings.filter((record) => !record.isBoolean);
      const checkboxGroups = plainGroups.filter((record) => record.isCheckbox);
      let eligible;
      if (trueFalse) {
        eligible = siblings.filter((record) => record.isBoolean);
        if (!eligible.length) {
          continue;
        }
      } else if (letters.length > 1) {
        eligible = checkboxGroups.length ? checkboxGroups : plainGroups;
      } else {
        eligible = siblings;
      }
      if (!eligible.length) {
        eligible = siblings;
      }

      // 同号题分布在多个大题时，优先处理当前屏幕上能看到的那一组
      let chosen = eligible;
      if (eligible.length > 1) {
        const visible = eligible.filter(isRecordOnScreen);
        if (visible.length) {
          chosen = visible;
        }
      }

      // 同号、同屏、却是不同类型（如是非 5 和单选 5 同时可见）时无法确定答案归属：
      // 只高亮，不点选，避免点错大题。
      const categories = new Set(
        chosen.map((record) => (record.isBoolean ? "b" : record.isCheckbox ? "c" : "r"))
      );
      const ambiguous = !trueFalse && letters.length <= 1 && categories.size > 1;
      let ambiguousHit = false;

      for (const record of chosen) {
        const { group, inputs, isCheckbox } = record;
        const hits = [];

        inputs.forEach((input, index) => {
          if (isDisabled(input)) {
            return;
          }
          const label = labelFor(input);
          if (!label) {
            return;
          }
          if (!isVisible(label) && !isVisible(input)) {
            return;
          }
          const labelText = (label.innerText || "").trim();
          const letter = optionLetter(label, input, index);
          let matched = false;
          if (letters.length) {
            matched = letters.includes(letter);
          } else if (trueFalse) {
            matched = matchTrueFalse(labelText, trueFalse === "true");
          } else {
            matched = matchTextAnswer(labelText, answerNorm, answerParts);
          }
          if (!matched) {
            return;
          }
          label.classList.add(HIGHLIGHT_CLASS);
          highlighted += 1;
          hits.push({ input, label, letter });
        });

        if (!hits.length) {
          continue;
        }
        matchedQuestions += 1;

        if (ambiguous) {
          ambiguousHit = true;
          continue;
        }

        // 屏幕外的题只高亮、不点选：避免页面自己滚动，
        // 也避免把「单选 1-4」的答案点到屏幕外「是非 1-4」上。
        if (!isRecordOnScreen(record)) {
          offscreenQuestions += 1;
          continue;
        }

        // 选项组是在这批答案之前就存在的，才允许点选。
        // 答案先到、选项后渲染时（常见于换页/SPA 刷新），本次只高亮，不点。
        const seenAt = groupSeenElements.get(group);
        const clickable = seenAt !== undefined && seenAt < answerBatchAt;
        if (!clickable) {
          staleQuestions += 1;
          continue;
        }

        for (const hit of hits) {
          if (hit.input.checked) {
            hit.label.classList.add(SELECTED_CLASS);
          }
        }

        let toClick = hits;
        if (!isCheckbox && hits.length > 1) {
          // 单选组只能有一个答案，避免连点导致最后停在错误项
          conflicts += 1;
          toClick = [pickPrimaryHit(hits, letters)];
        }
        for (const hit of toClick) {
          matchedOptions.push(hit);
        }

        // 多选组：明确写着字母、又不在答案里的已勾选项，顺手取消
        if (isCheckbox && letters.length) {
          for (const input of inputs) {
            if (isDisabled(input)) {
              continue;
            }
            const label = labelFor(input);
            if (!label || !input.checked) {
              continue;
            }
            const letter = explicitOptionLetter(label, input);
            if (letter && !letters.includes(letter)) {
              unselected.push({ input, label });
            }
          }
        }
      }
      if (ambiguousHit) {
        ambiguousQuestions += 1;
      }
    }

    // 填空题：按题号把答案填进屏幕内的输入框。
    // 只在页面确实有选项组时才做，避免把课程页的搜索框、评论框当成“第 1 题”。
    let filledBlanks = 0;
    if (autoClickEnabled && records.length) {
      const fillByNumber = new Map();
      for (const item of collectFillInputs()) {
        if (!answers.has(item.number)) {
          continue;
        }
        if (
          activeSections &&
          activeSections.size &&
          item.section &&
          !activeSections.has(item.section)
        ) {
          continue;
        }
        if (!isElementOnScreen(item.element)) {
          continue;
        }
        if (!fillByNumber.has(item.number)) {
          fillByNumber.set(item.number, []);
        }
        fillByNumber.get(item.number).push(item);
      }
      for (const [number, items] of fillByNumber) {
        const answer = String(answers.get(number) || "").trim();
        if (!answer) {
          continue;
        }
        const parts = splitFillAnswer(answer, items.length);
        items.forEach((item, index) => {
          const value = parts ? parts[index] : index === 0 ? answer : "";
          if (!value) {
            return;
          }
          if (elementValue(item.element) !== value) {
            setFillValue(item.element, value);
          }
          filledBlanks += 1;
        });
      }
    }

    const chaoxing = autoClickEnabled
      ? applyChaoxing(answers)
      : { questions: 0, picked: 0, filled: 0 };

    summary = {
      questions: matchedQuestions,
      highlighted,
      conflicts,
      stale: staleQuestions,
      offscreen: offscreenQuestions,
      ambiguous: ambiguousQuestions,
      filled: filledBlanks,
      cxQuestions: chaoxing.questions,
      cxPicked: chaoxing.picked,
      cxFilled: chaoxing.filled,
    };
    renderStatus();

    if (!highlighted && !filledBlanks && !chaoxing.picked && !chaoxing.filled) {
      const pageNumbers = records.map((record) => record.number).filter(Boolean);
      const answerEntries = Array.from(answers.entries());
      const inputCount = document.querySelectorAll(INPUT_SELECTOR).length;
      const reason = describeNoMatch(inputCount, pageNumbers, answerEntries);
      const version = extensionVersion();
      setStatus(
        `大肥鱼：有答案，但未匹配到选项 · ${reason}` + (version ? ` · v${version}` : ""),
        "warn"
      );
      return;
    }
    if (!autoClickEnabled) {
      return;
    }

    startClickJobs();
  }

  async function poll() {
    if (requestInFlight) {
      return;
    }
    requestInFlight = true;
    try {
      const response = await new Promise((resolve) => {
        chrome.runtime.sendMessage({ type: "getAnswers" }, (result) => {
          if (chrome.runtime.lastError) {
            resolve({ ok: false, error: chrome.runtime.lastError.message });
          } else {
            resolve(result || { ok: false, error: "no response" });
          }
        });
      });
      if (!response.ok) {
        setStatus("大肥鱼：未连接本机软件", "offline");
        clearTimeout(clickTimer);
        clickTimer = null;
        clearHighlights();
        activeSections = null;
        activeSignatures = null;
        matchedOptions = [];
        unselected = [];
        summary = null;
        lastData = null;
        lastUpdated = -1;
        return;
      }
      const data = response.data || {};
      if (data.updated === lastUpdated && lastData) {
        // 页面可能在后台把选项重置了，定期按真实状态刷新「已选」标记
        renderStatus();
        return;
      }
      // 记下答案到达的这一刻：此刻页面上已经有的选项组，才允许被这批答案点选
      noteGroups();
      activeSections = visibleSectionKeys();
      activeSignatures = visibleGroupSignatures();
      answerBatchAt = performance.now();
      lastUpdated = data.updated;
      lastData = data;
      // 新一批答案：重置点击预算和重试记录，允许重新点选
      clickBudgetUsed = 0;
      clickBudgetStart = Date.now();
      clickState = new WeakMap();
      applyAnswers(data);
      // 超星的富文本填空编辑器可能稍后才初始化，1.5 秒后再补一遍
      clearTimeout(fillRetryTimer);
      fillRetryTimer = setTimeout(() => {
        if (lastData) {
          applyAnswers(lastData);
        }
      }, 1500);
    } catch (error) {
      setStatus("大肥鱼：连接失败", "offline");
    } finally {
      requestInFlight = false;
    }
  }

  const observer = new MutationObserver((mutations) => {
    // 新选项组插入 DOM 时记录出现时间（即使还没有答案也要记）
    if (mutationAddsInputs(mutations)) {
      noteGroups();
    }
    if (!lastData) {
      return;
    }
    const relevant = mutations.some((mutation) => {
      const target = mutation.target;
      const element = target instanceof Element ? target : target.parentElement;
      return !(element && element.closest(`#${STATUS_ID}`));
    });
    if (!relevant) {
      return;
    }
    clearTimeout(reapplyTimer);
    reapplyTimer = setTimeout(() => {
      if (lastData) {
        applyAnswers(lastData);
      }
    }, 500);
  });

  window.addEventListener(
    "keydown",
    (event) => {
      if (event.altKey && event.shiftKey && event.code === DUMP_KEY_CODE) {
        event.preventDefault();
        event.stopPropagation();
        const text = JSON.stringify(collectDiagnostics(), null, 2);
        copyText(text).then((ok) => {
          if (ok) {
            setStatus("大肥鱼：诊断信息已复制到剪贴板，请发给我", "ok");
          } else {
            showDump(text);
            setStatus("大肥鱼：诊断信息已显示，请复制后发给我", "warn");
          }
        });
        return;
      }
      if (event.code !== TOGGLE_KEY_CODE || !event.altKey || !event.shiftKey) {
        return;
      }
      event.preventDefault();
      event.stopPropagation();
      autoClickEnabled = !autoClickEnabled;
      clickState = new WeakMap();
      clickBudgetUsed = 0;
      clickBudgetStart = Date.now();
      if (!autoClickEnabled) {
        clearTimeout(clickTimer);
        clickTimer = null;
      }
      if (autoClickEnabled && lastData) {
        applyAnswers(lastData);
      } else {
        renderStatus();
        if (!summary) {
          setStatus("大肥鱼：自动选择已暂停（Alt+Shift+P 恢复）", "warn");
        }
      }
    },
    true
  );

  function start() {
    // 内容脚本注入时页面上已有的选项组，算「早于答案出现」
    noteGroups();
    observer.observe(document.body || document.documentElement, {
      childList: true,
      subtree: true,
    });
    poll();
    setInterval(poll, 1500);
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", start, { once: true });
  } else {
    start();
  }
})();
