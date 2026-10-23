// 后台：统一代理 http://127.0.0.1:8765/answers
// - 500ms 内的重复请求走缓存（页面上有多个 iframe 时不用每次都发请求）
// - 3 秒超时，避免接口卡住导致内容脚本一直「请求中」
const ANSWER_URL = "http://127.0.0.1:8765/answers";
const CACHE_MS = 500;
const TIMEOUT_MS = 3000;

let cache = { at: 0, data: null };
let pending = null;

function loadAnswers() {
  if (cache.data && Date.now() - cache.at < CACHE_MS) {
    return Promise.resolve(cache.data);
  }
  if (pending) {
    return pending;
  }
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), TIMEOUT_MS);
  pending = fetch(ANSWER_URL, { cache: "no-store", signal: controller.signal })
    .then((response) => {
      if (!response.ok) {
        throw new Error("HTTP " + response.status);
      }
      return response.json();
    })
    .then((data) => {
      cache = { at: Date.now(), data };
      return data;
    })
    .finally(() => {
      clearTimeout(timer);
      pending = null;
    });
  return pending;
}

chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
  if (!message || message.type !== "getAnswers") {
    return;
  }
  loadAnswers()
    .then((data) => sendResponse({ ok: true, data }))
    .catch((error) => sendResponse({ ok: false, error: String((error && error.message) || error) }));
  return true;
});
