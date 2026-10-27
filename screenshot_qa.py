#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""大肥鱼搜题：监听截图文件夹，把新截图交给本地 Ollama 模型作答。

特点
----
* 只监听启动之后新出现的截图，不会把旧图片全部重跑一遍。
* 小巧的 Tkinter 窗口，支持一键置顶（Ctrl+T）。
* 零第三方依赖：使用 Windows 自带的 OCR 引擎和标准库 HTTP 客户端。
* 自动判断模型能力：视觉模型先做数学 OCR 转写公式，再交给答题模型；纯文本模型（如 qwen3.5-9b）用 Windows OCR。
* 模型回答流式显示，可随时停止。

运行：python screenshot_qa.py
"""

from __future__ import annotations

import argparse
import base64
import csv
import ctypes
import html as html_lib
import http.client
import http.server
import io
import json
import math
import os
import queue
import re
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time
import unicodedata
import urllib.request
from collections import deque
from ctypes import wintypes
from difflib import SequenceMatcher
from pathlib import Path
from urllib.parse import urlsplit
import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, messagebox, ttk
from tkinter.scrolledtext import ScrolledText

APP_NAME = "大肥鱼搜题"
if getattr(sys, "frozen", False):
    APP_DIR = Path(sys.executable).resolve().parent
    RESOURCE_DIR = Path(getattr(sys, "_MEIPASS", APP_DIR))
else:
    APP_DIR = Path(__file__).resolve().parent
    RESOURCE_DIR = APP_DIR
OCR_SCRIPT = RESOURCE_DIR / "ocr_win.ps1"
ICON_PNG = RESOURCE_DIR / "assets" / "deepseek-whale.png"
TEMP_DIR = APP_DIR / "temp"
BANK_FILE = APP_DIR / "题库.csv"

IMAGE_EXTS = {".png", ".jpg", ".jpeg", ".bmp", ".webp", ".gif"}
CREATE_NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)
POWERSHELL = Path(os.environ.get("SystemRoot", r"C:\Windows")) / "System32" / "WindowsPowerShell" / "v1.0" / "powershell.exe"

USER_HOME = Path.home()
DEFAULT_FOLDER = USER_HOME / "Pictures" / "Screenshots"
EXTRA_FOLDER = USER_HOME / "Downloads"
EXTRA_EXTS = {".jpeg"}
DEFAULT_BASE = "http://127.0.0.1:11434/v1"
DEFAULT_MODEL = "qwen3.5-9b"

ANSWER_TYPE_LABELS = {
    "answer": "答题",
    "summary": "总结",
    "reply": "高情商回复",
}
ANSWER_TYPE_BY_LABEL = {label: key for key, label in ANSWER_TYPE_LABELS.items()}

ANSWER_TYPE_PROMPTS = {
    "answer": "回答截图中的题目，只给答案，不要解释或括号补充。",
    "summary": "把页面上的文字归纳概括成要点。",
    "reply": "根据截图内容，帮我写一段高情商的回复。",
}
DEFAULT_ANSWER_TYPE = "answer"
DEFAULT_PROMPT = ANSWER_TYPE_PROMPTS[DEFAULT_ANSWER_TYPE]
LEGACY_PROMPTS = {
    "概括截图内容，提取关键文字、数字、报错或代码。",
    "总结截图内容，提炼关键信息，用要点列出。",
    "归纳概括截图页面中的文字内容，用要点列出。",
    "回答截图中的问题；没有明确问题时，给出关键结论。",
}
ALL_DEFAULT_PROMPTS = set(ANSWER_TYPE_PROMPTS.values()) | LEGACY_PROMPTS

MAX_OCR_CHARS = 4000
MAX_TOKENS = 1200
CONNECT_TIMEOUT = 8
REQUEST_TIMEOUT = 600
POLL_MS = 900
SCREENSHOT_HIDE_SECONDS = 15

WH_KEYBOARD_LL = 13
WM_KEYDOWN = 0x0100
WM_SYSKEYDOWN = 0x0104
WM_QUIT = 0x0012
VK_SHIFT = 0x10
VK_LWIN = 0x5B
VK_RWIN = 0x5C
VK_S = 0x53
VK_C = 0x43
VK_SNAPSHOT = 0x2C

# 配色
BG = "#f2f4f8"
CARD = "#ffffff"
BORDER = "#dde3ec"
TEXT = "#1e2430"
MUTED = "#6b7480"
ACCENT = "#2f6feb"
ACCENT_DK = "#2559c9"
OK = "#1a9d55"
WARN = "#c77d12"
ERR = "#d33a3a"
SOFT_BLUE = "#eaf1ff"
THUMB_BG = "#eef2f8"

OCR_ERRORS = {
    "no_engine": "系统没有可用的 OCR 识别引擎。请在 Windows 设置 → 时间和语言 → 语言中安装简体中文的“光学字符识别”组件。",
    "not_found": "截图文件已经不存在了。",
    "read_failed": "无法读取截图文件。",
    "init_failed": "Windows OCR 组件初始化失败。",
    "engine_failed": "无法创建 OCR 识别引擎。",
    "no_text": "这张截图里没有识别到文字。",
}

MODE_LABELS = {
    "auto": "自动检测（推荐）",
    "ocr": "OCR 文字（纯文本模型）",
    "vision": "数学 OCR（视觉模型）",
}
MODE_BY_LABEL = {v: k for k, v in MODE_LABELS.items()}

MATH_OCR_PROMPT = (
    "你是一个高等数学 OCR 引擎。请把图片里的题目完整转写为文本，"
    "数学公式尽量用 LaTeX（行内用 $...$），保留题号、上下标、极限、分式、"
    "根号、积分、矩阵、选项和填空位置。不要解答、不要总结、不要解释，"
    "不要遗漏任何公式或选项，只输出转写结果。"
)

VISION_MODEL_HINTS = (
    "vl", "vision", "gpt-4o", "gpt-4.1", "gpt-5", "gemini", "claude",
    "llava", "minicpm-v", "omni", "deepseek-flash",
)


def looks_like_vision_model(model: str) -> bool:
    name = str(model or "").lower()
    return any(hint in name for hint in VISION_MODEL_HINTS)

SYSTEM_PROMPTS_OCR = {
    "answer": (
        "你是一个答题助手。用户会提供从截图里识别出的题目。"
        "请逐题独立判断，只输出题号和答案："
        "判断题用“对”或“错”作答，不要写 A/B；"
        "选择题给出正确选项字母；填空题给出应填内容。"
        "不要默认选“对”或 A。每道题都重新判断题干是否成立；"
        "连续多题答案相同也可以，但必须是逐题判断的结果。"
        "特别注意“可以”“只需”“先……再……”“所有”“任何”等表述，"
        "判断是否存在绝对化或顺序错误。"
        "不要输出题目内容，不要写解释、依据、批注或括号补充。"
        "信息不足时只写“无法确定”。用中文，简洁。"
    ),
    "summary": (
        "你是一个页面文字归纳助手。请只根据提供的页面文字做归纳概括。"
        "严格按以下格式输出，不要写开场白、结束语或解释：\n"
        "主题：用一句话概括页面文字的主题\n"
        "要点：\n- 要点 1\n- 要点 2\n"
        "要求：不要描述截图、页面或布局，不要讨论 OCR，不要补充原文没有的信息，"
        "不要给建议或评价，不要编造。用中文，简洁。"
    ),
    "reply": (
        "你是一个高情商沟通助手。用户会提供从截图里识别出的对话或情境。"
        "请直接写出可以发送的回复文案，语气得体、真诚、有分寸；可以再给一个更委婉的备选。"
        "只输出回复本身，不要写“说明”“分析”或解释思路。"
        "不要描述截图，不要复述 OCR 原文，不要编造事实。"
        "OCR 可能有错字或漏字，信息不足时给一个安全的通用回复并说明。用中文。"
    ),
}

SYSTEM_PROMPTS_VISION = {
    "answer": (
        "你是一个答题助手。请根据截图内容逐题独立判断，只输出题号和答案："
        "判断题用“对”或“错”作答，不要写 A/B；"
        "选择题给出正确选项字母；填空题给出应填内容。"
        "不要默认选“对”或 A，每道题都重新判断题干是否成立。"
        "特别注意“可以”“只需”“先……再……”“所有”“任何”等表述，"
        "判断是否存在绝对化或顺序错误。"
        "不要输出题目内容，不要写解释、依据、批注或括号补充。"
        "信息不足时只写“无法确定”。用中文，简洁。"
    ),
    "summary": (
        "你是一个页面文字归纳助手。请只根据截图中的文字做归纳概括。"
        "严格按以下格式输出，不要写开场白、结束语或解释：\n"
        "主题：用一句话概括页面文字的主题\n"
        "要点：\n- 要点 1\n- 要点 2\n"
        "要求：不要描述画面或布局，不要补充原文没有的信息，不要给建议或评价，不要编造。"
        "用中文，简洁。"
    ),
    "reply": (
        "你是一个高情商沟通助手。请根据截图中的对话或情境，直接写出可以发送的回复文案，"
        "语气得体、真诚、有分寸；可以再给一个更委婉的备选。"
        "只输出回复本身，不要写“说明”“分析”或解释思路。不要描述截图，不要编造事实。"
        "信息不足时给一个安全的通用回复并说明。用中文。"
    ),
}


# ---------------------------------------------------------------------------
# 配置
# ---------------------------------------------------------------------------

def config_dir() -> Path:
    base = os.environ.get("APPDATA") or str(Path.home())
    return Path(base) / "ScreenshotQA"


def config_path() -> Path:
    return config_dir() / "settings.json"


DEFAULT_CONFIG = {
    "folder": str(DEFAULT_FOLDER),
    "base_url": DEFAULT_BASE,
    "api_key": "",
    "deepseek_no_think": True,
    "model": DEFAULT_MODEL,
    "mode": "auto",
    "answer_type": DEFAULT_ANSWER_TYPE,
    "prompt": DEFAULT_PROMPT,
    "topmost": False,
}


def load_config() -> dict:
    cfg = dict(DEFAULT_CONFIG)
    try:
        data = json.loads(config_path().read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return cfg
    if isinstance(data, dict):
        for key, default in DEFAULT_CONFIG.items():
            value = data.get(key)
            if isinstance(value, type(default)):
                cfg[key] = value
    if cfg["mode"] not in MODE_LABELS:
        cfg["mode"] = "auto"
    if cfg["answer_type"] not in ANSWER_TYPE_LABELS:
        cfg["answer_type"] = DEFAULT_ANSWER_TYPE
    if cfg["prompt"] in LEGACY_PROMPTS:
        cfg["prompt"] = ANSWER_TYPE_PROMPTS[cfg["answer_type"]]
    return cfg


def save_config(cfg: dict) -> None:
    try:
        directory = config_dir()
        directory.mkdir(parents=True, exist_ok=True)
        tmp = directory / "settings.tmp"
        tmp.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")
        tmp.replace(config_path())
    except OSError:
        pass


def prompt_for_type(answer_type: str) -> str:
    return ANSWER_TYPE_PROMPTS.get(answer_type, DEFAULT_PROMPT)


def normalize_match_text(value: str) -> str:
    text = unicodedata.normalize("NFKC", str(value)).lower()
    return re.sub(r"[\s\W_]+", "", text)


def extract_question_numbers(text: str) -> list[str]:
    cleaned = re.sub(r"(?<=\d)[ \t]+(?=\d)", "", text)
    numbers: list[str] = []
    for match in re.finditer(r"(?m)^\s*(\d{1,3})\s*[.．、]\s*", cleaned):
        number = match.group(1)
        if number not in numbers:
            numbers.append(number)
    return numbers


def extract_question_blocks(text: str) -> list[dict]:
    """按题号切分 OCR 文本，返回每道题的完整行。"""
    cleaned = re.sub(r"(?<=\d)[ \t]+(?=\d)", "", text)
    blocks: list[dict] = []
    current = None
    for raw_line in cleaned.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        match = re.match(r"^(\d{1,3})\s*[.．、]\s*(.*)$", line)
        if match:
            current = {"number": match.group(1), "lines": [line]}
            blocks.append(current)
        elif current is not None:
            current["lines"].append(line)
    return blocks


def parse_numbered_answers(text: str) -> dict[str, str]:
    answers: dict[str, str] = {}
    for raw_line in text.splitlines():
        line = raw_line.strip().strip("*").strip()
        if not line:
            continue
        line = re.sub(r"^[-•·]\s*", "", line)
        match = re.match(
            r"^\s*(?:第\s*)?(\d{1,3})(?!\d)\s*(?:题)?\s*[.．、:：]?\s*(.+?)\s*$",
            line,
        )
        if not match:
            continue
        value = match.group(2).strip().strip("*").strip()
        if value:
            answers[match.group(1)] = value
    return answers


def combine_question_answers(
    matches: dict[str, str], model_answer: str, numbers: list[str]
) -> str:
    """题库答案优先，模型答案只补未命中的题，最后按题号输出。"""
    model_answers = parse_numbered_answers(model_answer)
    missing = [number for number in numbers if number not in matches]
    if len(missing) == 1 and missing[0] not in model_answers:
        value = model_answer.strip()
        if value:
            model_answers[missing[0]] = value
    elif not model_answers and missing:
        lines = [line.strip() for line in model_answer.splitlines() if line.strip()]
        if len(lines) == len(missing):
            for number, line in zip(missing, lines):
                model_answers[number] = line
    if not model_answers and model_answer.strip():
        # 模型没有按题号输出时，保留它的完整回答，不能只剩题库命中的几题。
        return apply_bank_overrides(model_answer, matches)

    ordered_numbers = list(numbers)
    for number in model_answers:
        if number not in ordered_numbers:
            ordered_numbers.append(number)
    ordered_numbers.sort(key=lambda value: (0, int(value)) if value.isdigit() else (1, value))
    rows: list[str] = []
    for number in ordered_numbers:
        if number in matches:
            rows.append(f"{number}. {matches[number]}")
        elif number in model_answers:
            rows.append(f"{number}. {model_answers[number]}")
    if rows:
        return "\n".join(rows)
    return apply_bank_overrides(model_answer, matches)


def load_question_bank(path: Path) -> list[dict]:
    """读取 CSV 题库，列名支持 题号,题目,答案（题号可省略）。"""
    if not path.exists():
        return []
    try:
        raw = path.read_bytes()
    except OSError:
        return []

    text = None
    for encoding in ("utf-8-sig", "gbk"):
        try:
            text = raw.decode(encoding)
            break
        except UnicodeDecodeError:
            continue
    if text is None:
        return []

    try:
        sample = text[:4096]
        try:
            dialect = csv.Sniffer().sniff(sample, delimiters=",\t;")
        except csv.Error:
            dialect = csv.excel
        reader = csv.DictReader(io.StringIO(text), dialect=dialect)
        if not reader.fieldnames:
            return []
        headers = {str(name).strip().lower(): name for name in reader.fieldnames}

        def pick(*names: str):
            for name in names:
                if name in headers:
                    return headers[name]
            return None

        question_column = pick("题目", "问题", "question", "q")
        answer_column = pick("答案", "answer", "a")
        answer_text_column = pick("答案内容", "答案文本", "answer_text", "content")
        number_column = pick("题号", "编号", "number", "no", "id")
        if not question_column or not (answer_column or answer_text_column):
            return []

        entries: list[dict] = []
        for row in reader:
            question = str(row.get(question_column) or "").strip()
            answer = str(row.get(answer_column) or "").strip() if answer_column else ""
            answer_text = (
                str(row.get(answer_text_column) or "").strip()
                if answer_text_column else ""
            )
            if not question or (not answer and not answer_text):
                continue
            answer = re.sub(r"^答案\s*[:：]\s*", "", answer)
            number = ""
            if number_column:
                number = re.sub(r"\D", "", str(row.get(number_column) or ""))
            entries.append({
                "number": number,
                "question": question,
                "answer": answer,
                "answer_text": answer_text,
                "norm": normalize_match_text(question),
            })
        return entries
    except (csv.Error, UnicodeError):
        return []


def extract_option_map(text: str) -> dict[str, dict[str, str]]:
    """从 OCR 文本里提取每题当前的 A/B/C/D 选项内容。"""
    cleaned = re.sub(r"(?<=\d)[ \t]+(?=\d)", "", text)
    options: dict[str, dict[str, str]] = {}
    current: str | None = None
    for raw_line in cleaned.splitlines():
        line = raw_line.strip()
        question_match = re.match(r"^(\d{1,3})\s*[.．、]\s*(.*)$", line)
        if question_match:
            current = question_match.group(1)
            options.setdefault(current, {})
            continue
        option_match = re.match(r"^([A-Da-d&])\s*[.．、]?\s*(.+)$", line)
        if current and option_match:
            letter = option_match.group(1).upper()
            if letter == "&":
                letter = "B"
            options[current][letter] = option_match.group(2).strip()
    return options


def map_answer_text(answer_text: str, options: dict[str, str]) -> str:
    """把题库里的答案内容映射成当前选项字母；选项顺序变化时也能对上。"""
    def map_single(text: str) -> str:
        target = normalize_match_text(text)
        if not target or not options:
            return ""
        best_letter = ""
        best_score = 0.0
        for letter, option_text in options.items():
            option_norm = normalize_match_text(option_text)
            if not option_norm:
                continue
            if target in option_norm or option_norm in target:
                score = 1.0
            else:
                score = SequenceMatcher(None, target, option_norm, autojunk=False).ratio()
            if score > best_score:
                best_score = score
                best_letter = letter
        return best_letter if best_score >= 0.6 else ""

    parts = [part.strip() for part in re.split(r"[;；|]", answer_text) if part.strip()]
    if len(parts) > 1:
        letters = []
        for part in parts:
            letter = map_single(part)
            if not letter:
                return ""
            letters.append(letter)
        order = {letter: index for index, letter in enumerate("ABCD")}
        return "".join(sorted(set(letters), key=lambda value: order.get(value, 99)))
    return map_single(answer_text)


def match_question_bank(entries: list[dict], ocr_text: str) -> dict[str, str]:
    """把题库题目和 OCR 的每一行做相似度匹配，题号取当前截图里的题号。"""
    ocr_norm = normalize_match_text(ocr_text)
    if not ocr_norm:
        return {}
    cleaned = re.sub(r"(?<=\d)[ \t]+(?=\d)", "", ocr_text)
    line_items: list[tuple[str, str]] = []
    current_number = ""
    for raw_line in cleaned.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        question_match = re.match(r"^(\d{1,3})\s*[.．、]\s*(.*)$", line)
        if question_match:
            current_number = question_match.group(1)
        normalized = normalize_match_text(line)
        if normalized:
            line_items.append((normalized, current_number))
    if not line_items:
        return {}
    options_by_number = extract_option_map(ocr_text)

    def bigrams(value: str) -> set[str]:
        return {value[index:index + 2] for index in range(max(0, len(value) - 1))}

    ocr_bigrams = bigrams(ocr_norm)
    matches: dict[str, tuple[float, str]] = {}
    for entry in entries:
        entry_number = entry.get("number") or ""
        question_norm = entry.get("norm") or ""
        if len(question_norm) < 4:
            continue
        if question_norm in ocr_norm:
            score = 1.0
            best_number = next(
                (number for line, number in line_items if question_norm in line),
                entry_number,
            )
        else:
            question_bigrams = bigrams(question_norm)
            if not question_bigrams:
                continue
            coverage = sum(1 for gram in question_bigrams if gram in ocr_bigrams) / len(question_bigrams)
            if coverage < 0.3:
                continue
            score = 0.0
            best_number = entry_number
            for line, number in line_items:
                ratio = SequenceMatcher(None, question_norm, line, autojunk=False).ratio()
                if ratio > score:
                    score = ratio
                    best_number = number or entry_number
        number = best_number or entry_number
        if not number:
            continue
        answer = str(entry.get("answer") or "").strip()
        answer_text = str(entry.get("answer_text") or "").strip()
        mapped = ""
        if answer_text:
            mapped = map_answer_text(answer_text, options_by_number.get(number, {}))
            if mapped:
                answer = mapped
            elif not answer:
                answer = answer_text
        if not answer:
            continue
        threshold = 0.72 if len(question_norm) >= 12 else 0.8
        # 题目文字有 OCR 错字时，答案内容能对上当前选项也可以作为佐证。
        if score >= threshold or (mapped and score >= 0.68):
            previous = matches.get(number)
            if previous is None or score > previous[0]:
                matches[number] = (score, answer)
    return {number: answer for number, (score, answer) in matches.items()}


def format_bank_answers(matches: dict[str, str]) -> str:
    def sort_key(item):
        number = item[0]
        return (0, int(number)) if number.isdigit() else (1, number)

    return "\n".join(
        f"{number}. {answer}" for number, answer in sorted(matches.items(), key=sort_key)
    )


def apply_bank_overrides(answer: str, matches: dict[str, str]) -> str:
    if not matches:
        return answer
    lines = answer.splitlines()
    result: list[str] = []
    seen: set[str] = set()
    for line in lines:
        match = re.match(r"^\s*(\d{1,3})\s*[.．、]\s*(.*)$", line)
        if match and match.group(1) in matches:
            number = match.group(1)
            result.append(f"{number}. {matches[number]}")
            seen.add(number)
        else:
            result.append(line)
    for number in sorted(matches, key=lambda value: int(value) if value.isdigit() else 9999):
        if number not in seen:
            result.append(f"{number}. {matches[number]}")
    return "\n".join(result).strip()


def clean_html_cell(cell: str) -> str:
    text = re.sub(r"<[^>]+>", "", cell)
    text = html_lib.unescape(text)
    return re.sub(r"\s+", " ", text).strip()


def parse_html_question_bank(path: Path, stats: dict | None = None) -> list[dict]:
    """解析题库后台保存的 HTML 表格，提取题目和正确答案内容。"""
    if stats is not None:
        stats.update({"rows": 0, "unique": 0, "duplicates": 0, "invalid": 0})
    try:
        raw = path.read_bytes()
    except OSError:
        return []
    text = None
    for encoding in ("utf-8-sig", "gbk"):
        try:
            text = raw.decode(encoding)
            break
        except UnicodeDecodeError:
            continue
    if text is None:
        return []

    rows = re.findall(
        r'<tr[^>]*class="[^"]*el-table__row[^"]*"[^>]*>(.*?)</tr>',
        text,
        re.S | re.I,
    )
    entries: list[dict] = []
    seen: set[str] = set()
    duplicates = 0
    invalid = 0
    for row in rows:
        cells = [
            clean_html_cell(cell)
            for cell in re.findall(r"<td\b[^>]*>(.*?)</td>", row, re.S | re.I)
        ]
        if len(cells) < 6:
            invalid += 1
            continue
        question = cells[1]
        answer_text = cells[4]
        if not question or not answer_text:
            invalid += 1
            continue
        answer_text = re.sub(r"\s*[;；]\s*", "；", answer_text).strip()
        key = normalize_match_text(question)
        if not key:
            invalid += 1
            continue
        if key in seen:
            duplicates += 1
            continue
        seen.add(key)
        entries.append({
            "number": "",
            "question": question,
            "answer": "",
            "answer_text": answer_text,
            "norm": key,
        })
    if stats is not None:
        stats.update({
            "rows": len(rows),
            "unique": len(entries),
            "duplicates": duplicates,
            "invalid": invalid,
        })
    return entries


def merge_question_bank(existing: list[dict], imported: list[dict]) -> tuple[list[dict], int, int, int]:
    unique_existing: list[dict] = []
    seen: set[str] = set()
    removed = 0
    for entry in existing:
        key = normalize_match_text(entry.get("question") or "")
        if not key or key in seen:
            removed += 1
            continue
        seen.add(key)
        unique_existing.append(entry)
    existing[:] = unique_existing

    by_key = {normalize_match_text(entry.get("question") or ""): entry for entry in existing}
    added = 0
    updated = 0
    for item in imported:
        key = normalize_match_text(item.get("question") or "")
        if not key:
            continue
        current = by_key.get(key)
        if current is not None:
            if item.get("answer_text") and current.get("answer_text") != item["answer_text"]:
                current["answer_text"] = item["answer_text"]
                updated += 1
            if item.get("answer") and not current.get("answer"):
                current["answer"] = item["answer"]
        else:
            existing.append(item)
            by_key[key] = item
            added += 1
    return existing, added, updated, removed


def write_question_bank(path: Path, entries: list[dict]) -> bool:
    try:
        temp_path = path.parent / (path.name + ".tmp")
        with temp_path.open("w", encoding="utf-8-sig", newline="") as handle:
            writer = csv.writer(handle)
            writer.writerow(["题号", "题目", "答案", "答案内容"])
            for entry in entries:
                writer.writerow([
                    entry.get("number") or "",
                    entry.get("question") or "",
                    entry.get("answer") or "",
                    entry.get("answer_text") or "",
                ])
        temp_path.replace(path)
        return True
    except OSError:
        return False


# ---------------------------------------------------------------------------
# 小工具
# ---------------------------------------------------------------------------

def human_size(num: int) -> str:
    size = float(num)
    for unit in ("B", "KB", "MB"):
        if size < 1024:
            return f"{size:.0f} {unit}" if unit == "B" else f"{size:.1f} {unit}"
        size /= 1024
    return f"{size:.1f} GB"


def shorten(text: str, limit: int = 46) -> str:
    if len(text) <= limit:
        return text
    head = max(8, limit // 2 - 2)
    tail = max(8, limit - head - 1)
    return text[:head] + "…" + text[-tail:]


def chat_url(base: str) -> str:
    value = base.strip().rstrip("/")
    if value.endswith("/chat/completions"):
        return value
    if not value.endswith("/v1"):
        value += "/v1"
    return value + "/chat/completions"


def api_root(base: str) -> str:
    value = base.strip().rstrip("/")
    for suffix in ("/v1/chat/completions", "/chat/completions", "/v1"):
        if value.endswith(suffix):
            value = value[: -len(suffix)]
            break
    return value.rstrip("/")


def is_ollama_base(base_url: str) -> bool:
    try:
        parts = urlsplit(base_url)
        host = (parts.hostname or "").lower()
        port = parts.port or (443 if parts.scheme == "https" else 80)
    except ValueError:
        return False
    return host in {"127.0.0.1", "localhost", "::1"} and port == 11434


def mime_for(path: Path) -> str:
    return {
        ".png": "image/png",
        ".jpg": "image/jpeg",
        ".jpeg": "image/jpeg",
        ".webp": "image/webp",
        ".bmp": "image/bmp",
        ".gif": "image/gif",
    }.get(path.suffix.lower(), "image/png")


def open_chat_connection(url: str, body: bytes, accept: str = "text/event-stream",
                         api_key: str = ""):
    """建立到模型服务的连接：连接阶段 8 秒超时，读取阶段允许长时间生成。"""
    parts = urlsplit(url)
    if parts.scheme not in ("http", "https") or not parts.hostname:
        raise ValueError("接口地址无效")
    port = parts.port or (443 if parts.scheme == "https" else 80)
    connection_class = (
        http.client.HTTPSConnection if parts.scheme == "https" else http.client.HTTPConnection
    )
    connection = connection_class(parts.hostname, port, timeout=CONNECT_TIMEOUT)
    try:
        connection.connect()
        if connection.sock is not None:
            connection.sock.settimeout(REQUEST_TIMEOUT)
        path = parts.path or "/"
        if parts.query:
            path += "?" + parts.query
        headers = {
            "Content-Type": "application/json",
            "Accept": accept,
        }
        if api_key:
            headers["Authorization"] = f"Bearer {api_key}"
        connection.request(
            "POST",
            path,
            body=body,
            headers=headers,
        )
        return connection, connection.getresponse()
    except Exception:
        connection.close()
        raise


def detect_vision(base_url: str, model: str, timeout: float = 4.0):
    """查询 Ollama 的模型能力，返回 (是否支持视觉, 能力列表)。只读取元数据。"""
    payload = json.dumps({"name": model}).encode("utf-8")
    request = urllib.request.Request(
        api_root(base_url) + "/api/show",
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=timeout) as response:
        data = json.loads(response.read().decode("utf-8", "replace"))
    capabilities = data.get("capabilities") or []
    return ("vision" in capabilities), capabilities


def run_ocr(path: Path, timeout: int = 90) -> dict:
    """调用 ocr_win.ps1，用 Windows 自带 OCR 提取截图文字。"""
    if not OCR_SCRIPT.exists():
        return {"ok": False, "error": f"缺少 OCR 组件：{OCR_SCRIPT}"}
    fd, temp_name = tempfile.mkstemp(prefix="screenshot_qa_ocr_", suffix=".json")
    os.close(fd)
    try:
        command = [
            str(POWERSHELL),
            "-NoProfile",
            "-NonInteractive",
            "-ExecutionPolicy",
            "Bypass",
            "-File",
            str(OCR_SCRIPT),
            "-Path",
            str(path),
            "-OutFile",
            temp_name,
        ]
        try:
            subprocess.run(
                command,
                capture_output=True,
                timeout=timeout,
                creationflags=CREATE_NO_WINDOW,
            )
        except subprocess.TimeoutExpired:
            return {"ok": False, "error": "OCR 识别超时（超过 90 秒）。"}
        except OSError as exc:
            return {"ok": False, "error": f"无法启动 Windows OCR 组件：{exc}"}

        try:
            raw = Path(temp_name).read_text(encoding="utf-8-sig")
            data = json.loads(raw)
        except (OSError, ValueError):
            return {"ok": False, "error": "OCR 组件没有返回有效结果。"}

        if data.get("ok"):
            text = data.get("text") or ""
            lines = data.get("lines") or []
            if isinstance(lines, list) and lines:
                heights = []
                for item in lines:
                    try:
                        heights.append(max(1.0, float(item.get("h") or 0)))
                    except (TypeError, ValueError):
                        heights.append(1.0)
                median_height = sorted(heights)[len(heights) // 2]
                row_tolerance = max(8.0, median_height * 0.7)
                ordered = sorted(
                    lines,
                    key=lambda item: (
                        round(float(item.get("y") or 0) / row_tolerance),
                        float(item.get("x") or 0),
                    ),
                )
                joined = "\n".join(
                    str(item.get("text") or "").strip()
                    for item in ordered
                    if str(item.get("text") or "").strip()
                )
                if joined:
                    text = joined
            return {
                "ok": True,
                "text": text,
                "meta": data,
            }

        code = data.get("error_code") or ""
        message = OCR_ERRORS.get(code, "OCR 识别失败。")
        detail = data.get("detail") or ""
        if detail:
            message += f"\n技术细节：{detail}"
        return {"ok": False, "error": message}
    finally:
        try:
            os.unlink(temp_name)
        except OSError:
            pass


def enable_dpi_awareness() -> None:
    if sys.platform != "win32":
        return
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass


class AnalysisError(Exception):
    pass


class NativeUnavailable(Exception):
    pass


class Cancelled(Exception):
    pass


class AnswerHttpHandler(http.server.BaseHTTPRequestHandler):
    server_version = "ScreenshotQA/1.0"

    def log_message(self, format, *args):
        pass

    def _send(self, status: int, payload: dict) -> None:
        body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "*")
        self.end_headers()

    def do_GET(self):
        app = getattr(self.server, "app", None)
        path = urlsplit(self.path).path
        if app is None:
            self._send(503, {"error": "app not ready"})
            return
        if path == "/answers":
            self._send(200, {
                "updated": app._plugin_updated,
                "answers": app._plugin_answers,
            })
        elif path == "/health":
            self._send(200, {"ok": True})
        else:
            self._send(404, {"error": "not found"})


# ---------------------------------------------------------------------------
# 主窗口
# ---------------------------------------------------------------------------

class ScreenshotQA(tk.Tk):
    def __init__(self, args: argparse.Namespace):
        super().__init__()

        self.cfg = load_config()
        if args.folder:
            self.cfg["folder"] = str(args.folder)
        if args.base:
            self.cfg["base_url"] = args.base
        if args.model:
            self.cfg["model"] = args.model

        self.folder = Path(self.cfg["folder"]).expanduser()
        try:
            self.folder.mkdir(parents=True, exist_ok=True)
        except OSError:
            pass
        self.base_url = str(self.cfg["base_url"])
        self.api_key = str(self.cfg.get("api_key") or "")
        self.deepseek_no_think = bool(self.cfg.get("deepseek_no_think", True))
        self.model = str(self.cfg["model"])
        self.mode = str(self.cfg["mode"])
        self.answer_type = str(self.cfg["answer_type"])
        self.topmost = bool(self.cfg["topmost"])
        self.vision_supported = None
        self.native_available = True

        self.watching = True
        self.busy = False
        self._clearing = False
        self.answer_text = ""
        self.last_image: Path | None = None
        self.current_image: Path | None = None
        self.analyzed = 0
        self.stage_kind = "idle"
        self.started_at = 0.0
        self.ocr_cache: dict[tuple, str] = {}
        self.bank_path = BANK_FILE
        self._bank_cache: tuple[int, list[dict]] | None = None

        self._seen: dict[Path, tuple] = {}
        self._probe: dict[Path, tuple] = {}
        self._pending: deque[Path] = deque()
        self._cancel = threading.Event()
        self._ui_queue: queue.Queue = queue.Queue()
        self._connection = None
        self._connection_lock = threading.Lock()
        self._thumb_image = None
        self._window_icon = None
        self._closing = False
        self._folder_error = ""
        self._answer_rendered = False
        self._screenshot_hidden = False
        self._screenshot_deadline = 0.0
        self._clipboard_seq = 0
        self._hotkey_last = 0.0
        self._hwnd = 0
        self._hud_hwnd = 0
        self._hud_was_visible = False
        self.hud: tk.Toplevel | None = None
        self.hud_text: tk.Text | None = None
        self._hud_drag_offset = (0, 0)
        self._answer_server = None
        self._plugin_answers: list[dict] = []
        self._plugin_updated = 0.0
        self._hook_handle = None
        self._hook_thread_id = 0
        self._hook_proc = None

        self.title(APP_NAME)
        self.configure(bg=BG)
        self.minsize(520, 560)
        self._setup_window()
        self._setup_fonts()
        self._setup_style()
        self._build_ui()
        self._apply_window_icon()
        self._apply_topmost()
        self._bind_keys()
        self._reset_baseline(show_newest=True)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

        self.after(120, self._pump)
        self.after(250, self._start_answer_server)
        self.after(300, self._detect_async)
        self.after(350, self._start_screenshot_hook)
        self.after(600, self._poll_folder)

    # -- 外观 ---------------------------------------------------------------

    def _apply_window_icon(self) -> None:
        try:
            image = tk.PhotoImage(file=str(ICON_PNG))
        except (tk.TclError, OSError):
            return
        self._window_icon = image
        try:
            self.iconphoto(True, image)
        except tk.TclError:
            pass

    def _setup_window(self) -> None:
        try:
            dpi = self.winfo_fpixels("1i")
            self.tk.call("tk", "scaling", dpi / 72.0)
        except tk.TclError:
            pass
        width = 640
        screen_w = self.winfo_screenwidth()
        screen_h = self.winfo_screenheight()
        height = min(700, max(560, screen_h - 120))
        x = max(0, screen_w - width - 44)
        y = 56
        if y + height > screen_h:
            y = max(0, screen_h - height - 40)
        self.geometry(f"{width}x{height}+{x}+{y}")

    def _setup_fonts(self) -> None:
        families = set(tkfont.families(self))
        self.font_family = "Microsoft YaHei UI"
        if self.font_family not in families:
            self.font_family = "Microsoft YaHei" if "Microsoft YaHei" in families else "Segoe UI"
        for name in ("TkDefaultFont", "TkTextFont", "TkMenuFont", "TkHeadingFont"):
            try:
                tkfont.nametofont(name).configure(family=self.font_family, size=10)
            except tk.TclError:
                pass
        self.mono_family = "Cascadia Mono"
        if self.mono_family not in families:
            self.mono_family = "Consolas" if "Consolas" in families else "Courier New"

    def _setup_style(self) -> None:
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure("TButton", font=(self.font_family, 9), padding=(10, 6),
                        background=CARD, foreground=TEXT, bordercolor=BORDER,
                        lightcolor=CARD, darkcolor=CARD, relief="flat", focusthickness=0)
        style.map("TButton",
                  background=[("active", "#eef2f9"), ("pressed", "#e3e9f4"), ("disabled", "#f5f7fa")],
                  foreground=[("disabled", "#a7aeb8")],
                  bordercolor=[("disabled", "#e6eaf1")])
        style.configure("Accent.TButton", font=(self.font_family, 9, "bold"), padding=(10, 6),
                        background=ACCENT, foreground="#ffffff", bordercolor=ACCENT,
                        lightcolor=ACCENT, darkcolor=ACCENT, relief="flat")
        style.map("Accent.TButton",
                  background=[("active", ACCENT_DK), ("pressed", ACCENT_DK), ("disabled", "#a8c0f2")],
                  foreground=[("disabled", "#ffffff")],
                  bordercolor=[("disabled", "#a8c0f2")])
        style.configure("TEntry", padding=5, fieldbackground=CARD, bordercolor=BORDER,
                        lightcolor=BORDER, darkcolor=BORDER)
        style.configure("TCombobox", padding=4, fieldbackground=CARD, background=CARD,
                        bordercolor=BORDER, arrowcolor=MUTED)
        style.map("TCombobox", fieldbackground=[("readonly", CARD)], foreground=[("readonly", TEXT)])
        style.configure("Vertical.TScrollbar", background="#c8d1de", troughcolor=CARD,
                        bordercolor=CARD, arrowcolor=MUTED, relief="flat", arrowsize=12)
        style.map("Vertical.TScrollbar", background=[("active", "#aeb9c9")])

    def _card(self, parent) -> tk.Frame:
        return tk.Frame(parent, bg=CARD, highlightbackground=BORDER, highlightthickness=1)

    def _build_ui(self) -> None:
        pad = 16

        root = tk.Frame(self, bg=BG)
        root.pack(fill="both", expand=True)

        # 顶栏 --------------------------------------------------------------
        header = tk.Frame(root, bg=BG)
        header.pack(fill="x", padx=pad, pady=(14, 8))
        header.columnconfigure(0, weight=1)

        title_box = tk.Frame(header, bg=BG)
        title_box.grid(row=0, column=0, sticky="w")
        tk.Label(title_box, text="大肥鱼搜题", bg=BG, fg=TEXT,
                 font=(self.font_family, 15, "bold")).pack(anchor="w")
        self.subtitle = tk.Label(
            title_box,
            text=f"自动监听新截图 · {self.model}",
            bg=BG, fg=MUTED, font=(self.font_family, 9),
        )
        self.subtitle.pack(anchor="w", pady=(2, 0))

        actions = tk.Frame(header, bg=BG)
        actions.grid(row=0, column=1, sticky="e")
        self.pin_button = ttk.Button(actions, text="置顶：关", width=8, command=self.toggle_topmost)
        self.pin_button.pack(side="left", padx=(0, 6))
        self.settings_button = ttk.Button(actions, text="设置", width=6, command=self.open_settings)
        self.settings_button.pack(side="left")

        # 当前截图卡片 ------------------------------------------------------
        preview = self._card(root)
        preview.pack(fill="x", padx=pad, pady=(0, 9))
        preview.columnconfigure(1, weight=1)

        thumb_holder = tk.Frame(preview, bg=THUMB_BG, width=220, height=140)
        thumb_holder.grid(row=0, column=0, rowspan=2, padx=12, pady=12, sticky="n")
        thumb_holder.grid_propagate(False)
        self.thumb = tk.Label(thumb_holder, bg=THUMB_BG, fg=MUTED, text="暂无截图",
                              font=(self.font_family, 9), cursor="hand2")
        self.thumb.pack(fill="both", expand=True)
        self.thumb.bind("<Button-1>", lambda _event: self.open_current_image())

        info = tk.Frame(preview, bg=CARD)
        info.grid(row=0, column=1, sticky="nsew", pady=(12, 0), padx=(0, 12))
        self.file_label = tk.Label(info, text="等待新的截图…", bg=CARD, fg=TEXT,
                                   font=(self.font_family, 10, "bold"),
                                   anchor="w", justify="left", wraplength=300)
        self.file_label.pack(fill="x")
        self.meta_label = tk.Label(info, text="把截图保存到监听目录即可自动分析",
                                   bg=CARD, fg=MUTED, font=(self.font_family, 8), anchor="w")
        self.meta_label.pack(fill="x", pady=(3, 0))
        self.stage_label = tk.Label(
            info, text="● 就绪", bg=CARD, fg=MUTED,
            font=(self.font_family, 9), anchor="w", justify="left", wraplength=300,
        )
        self.stage_label.pack(fill="x", pady=(7, 0))

        action_box = tk.Frame(preview, bg=CARD)
        action_box.grid(row=1, column=1, sticky="w", pady=(6, 12), padx=(0, 12))
        self.reanalyze_button = ttk.Button(action_box, text="重新分析", width=9,
                                           command=self.reanalyze, state="disabled")
        self.reanalyze_button.pack(side="left")
        self.stop_button = ttk.Button(action_box, text="停止", width=6,
                                      command=self.cancel_current, state="disabled")
        self.stop_button.pack(side="left", padx=(6, 0))
        self.clear_button = ttk.Button(action_box, text="清空", width=6,
                                       command=self.clear_current_page)
        self.clear_button.pack(side="left", padx=(6, 0))

        # 提问 --------------------------------------------------------------
        prompt_card = self._card(root)
        prompt_card.pack(fill="x", padx=pad, pady=(0, 9))
        tk.Label(prompt_card, text="提问", bg=CARD, fg=MUTED,
                 font=(self.font_family, 9)).pack(side="left", padx=(12, 8), pady=10)
        self.prompt_var = tk.StringVar(value=str(self.cfg["prompt"]))
        self.prompt_entry = tk.Entry(
            prompt_card, textvariable=self.prompt_var, font=(self.font_family, 9),
            bg=CARD, fg=TEXT, relief="flat", insertbackground=ACCENT,
            highlightthickness=0, bd=0,
        )
        self.prompt_entry.pack(side="left", fill="x", expand=True, pady=8, padx=(0, 12))
        self.prompt_entry.bind("<Return>", lambda _event: self.reanalyze())

        # 回答 --------------------------------------------------------------
        answer_card = self._card(root)
        answer_card.pack(fill="both", expand=True, padx=pad, pady=(0, 9))

        answer_head = tk.Frame(answer_card, bg=CARD)
        answer_head.pack(fill="x", padx=12, pady=(9, 0))
        tk.Label(answer_head, text="回答", bg=CARD, fg=TEXT,
                 font=(self.font_family, 10, "bold")).pack(side="left")
        self.mode_badge = tk.Label(answer_head, text=self._mode_text(), bg=SOFT_BLUE, fg=ACCENT,
                                   font=(self.font_family, 8), padx=8, pady=2)
        self.mode_badge.pack(side="left", padx=(8, 0))
        self.copy_button = ttk.Button(answer_head, text="复制", width=5, command=self.copy_answer)
        self.copy_button.pack(side="right")

        self.text = ScrolledText(
            answer_card, wrap="word", font=(self.font_family, 10),
            bg=CARD, fg=TEXT, bd=0, relief="flat", padx=14, pady=8,
            insertbackground=TEXT, selectbackground="#cfe0ff",
            highlightthickness=0, spacing1=2, spacing3=4, height=8,
        )
        self.text.pack(fill="both", expand=True, padx=(8, 2), pady=(4, 6))
        self.text.configure(state="disabled", cursor="arrow")
        self.text.tag_configure("answer", foreground=TEXT, font=(self.font_family, 10),
                                spacing1=2, spacing3=5)
        self.text.tag_configure("meta", foreground=MUTED, font=(self.font_family, 8), spacing3=8)
        self.text.tag_configure("muted", foreground="#8b94a3", font=(self.font_family, 10),
                                spacing1=4, spacing3=6)
        self.text.tag_configure("error", foreground=ERR, font=(self.font_family, 10),
                                spacing1=4, spacing3=6)
        self.text.tag_configure("code", foreground="#22303f", background="#f3f5fa",
                                font=(self.mono_family, 9), lmargin1=12, lmargin2=12,
                                spacing1=3, spacing3=3)
        self.text.tag_configure("inline", foreground="#22303f", background="#f3f5fa",
                                font=(self.mono_family, 9))
        self.text.tag_configure("strong", foreground=TEXT, font=(self.font_family, 10, "bold"))
        self._set_answer_placeholder(
            "等待新的截图…\n\n"
            "把截图保存到监听目录（例如按 Win+Shift+S 或 Fn+Win+C 截图），程序会自动识别并在这里显示回答。\n"
            "也可以点击上方「重新分析」重跑当前这张截图。"
        )

        # 底栏 --------------------------------------------------------------
        status = tk.Frame(root, bg=BG)
        status.pack(side="bottom", fill="x", padx=pad, pady=(0, 10), before=answer_card)
        self.status_dot = tk.Label(status, text="●", bg=BG, fg=OK, font=(self.font_family, 9))
        self.status_dot.pack(side="left")
        self.status_text = tk.Label(status, text="监听中", bg=BG, fg=MUTED,
                                    font=(self.font_family, 9))
        self.status_text.pack(side="left", padx=(4, 8))
        self.folder_label = tk.Label(status, text=shorten(str(self.folder), 36), bg=BG, fg=MUTED,
                                     font=(self.font_family, 8), anchor="w")
        self.count_label = tk.Label(status, text="已分析 0 张", bg=BG, fg=MUTED,
                                    font=(self.font_family, 8))
        self.pause_button = ttk.Button(status, text="暂停", width=6, command=self.toggle_pause)
        # 先给右侧按钮和计数分配空间，中间的路径再占用剩余宽度，避免按钮被挤掉。
        self.pause_button.pack(side="right")
        self.count_label.pack(side="right", padx=(8, 8))
        self.folder_label.pack(side="left", fill="x", expand=True)

    def _bind_keys(self) -> None:
        self.bind("<Control-t>", lambda _event: self.toggle_topmost())
        self.bind("<Control-T>", lambda _event: self.toggle_topmost())
        self.bind("<Control-r>", lambda _event: self.reanalyze())
        self.bind("<Control-R>", lambda _event: self.reanalyze())
        self.bind("<Escape>", lambda _event: self.cancel_current())

    # -- 答案浮层 -----------------------------------------------------------

    def toggle_hud(self) -> None:
        if self.hud is not None and self.hud.winfo_exists():
            self.hud.destroy()
            self.hud = None
            self.hud_text = None
            self._hud_hwnd = 0
            self._hud_was_visible = False
            self.hud_button.configure(style="TButton")
            return
        self._create_hud()
        self.hud_button.configure(style="Accent.TButton")
        self._refresh_hud()

    def _create_hud(self) -> None:
        hud = tk.Toplevel(self)
        hud.overrideredirect(True)
        hud.attributes("-topmost", True)
        hud.attributes("-alpha", 0.98)
        hud.configure(bg=ACCENT)

        outer = tk.Frame(hud, bg="#111827")
        outer.pack(fill="both", expand=True, padx=1, pady=1)
        header = tk.Frame(outer, bg="#111827")
        header.pack(fill="x", padx=10, pady=(8, 0))
        title = tk.Label(
            header, text="答案浮层 · 拖动移动", bg="#111827", fg="#9ca3af",
            font=(self.font_family, 8),
        )
        title.pack(side="left")
        close = tk.Label(
            header, text="×", bg="#111827", fg="#d1d5db",
            font=(self.font_family, 12, "bold"), cursor="hand2",
        )
        close.pack(side="right")
        close.bind("<Button-1>", lambda _event: self.toggle_hud())

        self.hud_text = tk.Text(
            outer, width=22, height=1, wrap="word", font=(self.font_family, 13, "bold"),
            bg="#111827", fg="#f9fafb", insertbackground="#f9fafb",
            bd=0, highlightthickness=0, padx=8, pady=4,
        )
        self.hud_text.pack(fill="both", expand=True, padx=10, pady=(2, 10))
        self.hud_text.configure(state="disabled", cursor="arrow")
        self.hud = hud

        for widget in (hud, outer, header, title, self.hud_text):
            widget.bind("<ButtonPress-1>", self._hud_drag_start)
            widget.bind("<B1-Motion>", self._hud_drag_move)

        self.update_idletasks()
        width = 300
        x = max(12, self.winfo_rootx() - width - 14)
        y = self.winfo_rooty() + 90
        hud.geometry(f"{width}x140+{x}+{y}")
        hud.update_idletasks()
        try:
            self._hud_hwnd = int(hud.wm_frame(), 16)
        except (tk.TclError, ValueError):
            self._hud_hwnd = 0

    def _refresh_hud(self) -> None:
        if not self.hud or not self.hud_text:
            return
        raw = self.answer_text.strip()
        if not raw:
            lines = ["等待截图…"]
        else:
            lines = [line.strip() for line in raw.splitlines() if line.strip()]
            answer_lines = [
                line for line in lines
                if re.match(r"^\d{1,3}\s*[.．、]\s*", line)
            ]
            if answer_lines:
                lines = answer_lines
            if len(lines) > 12:
                lines = lines[:12] + ["…"]
        text = "\n".join(lines)
        self.hud_text.configure(state="normal")
        self.hud_text.delete("1.0", "end")
        self.hud_text.insert("1.0", text)
        self.hud_text.configure(state="disabled", height=min(12, max(1, len(lines))))
        self.hud.update_idletasks()
        width = 300
        height = max(90, self.hud_text.winfo_reqheight() + 58)
        try:
            x = self.hud.winfo_x()
            y = self.hud.winfo_y()
        except tk.TclError:
            return
        self.hud.geometry(f"{width}x{height}+{x}+{y}")

    def _hud_drag_start(self, event) -> None:
        if not self.hud:
            return
        self._hud_drag_offset = (
            event.x_root - self.hud.winfo_x(),
            event.y_root - self.hud.winfo_y(),
        )

    def _hud_drag_move(self, event) -> None:
        if not self.hud:
            return
        x = event.x_root - self._hud_drag_offset[0]
        y = event.y_root - self._hud_drag_offset[1]
        x = max(0, min(x, self.winfo_screenwidth() - 120))
        y = max(0, min(y, self.winfo_screenheight() - 80))
        self.hud.geometry(f"+{x}+{y}")

    # -- 浏览器插件答案接口 -------------------------------------------------

    def _start_answer_server(self) -> None:
        if self._answer_server is not None:
            return
        try:
            server = http.server.ThreadingHTTPServer(("127.0.0.1", 8765), AnswerHttpHandler)
            server.daemon_threads = True
            server.app = self
            threading.Thread(target=server.serve_forever, daemon=True).start()
            self._answer_server = server
        except OSError:
            self._answer_server = None
            self.after(100, self._notify_server_conflict)

    def _notify_server_conflict(self) -> None:
        if self._closing:
            return
        messagebox.showwarning(
            APP_NAME,
            "8765 端口已被占用，可能还有一个旧的大肥鱼搜题窗口在运行。\n"
            "请先完全关闭旧窗口，再重新启动，否则插件可能一直读到旧答案。",
            parent=self,
        )

    def _set_plugin_answers(self, answer: str) -> None:
        entries: list[dict] = []
        for raw_line in answer.splitlines():
            line = raw_line.strip().strip("*").strip()
            if not line:
                continue
            line = re.sub(r"^[-•·]\s*", "", line)
            match = re.match(
                r"^\s*(?:第\s*)?(\d{1,3})(?!\d)\s*(?:题)?\s*[.．、:：]?\s*(.+?)\s*$",
                line,
            )
            if not match:
                continue
            value = match.group(2).strip().strip("*").strip()
            if not value:
                continue
            entries.append({
                "number": match.group(1),
                "answer": value,
            })
        self._plugin_answers = entries
        self._plugin_updated = time.time()

    # -- 截图快捷键隐藏（Win+Shift+S / Fn+Win+C） ---------------------------

    def _start_screenshot_hook(self) -> None:
        if sys.platform != "win32" or self._hook_handle:
            return
        try:
            self._hwnd = int(self.wm_frame(), 16)
        except (tk.TclError, ValueError):
            self._hwnd = 0
        if not self._hwnd:
            return
        threading.Thread(target=self._screenshot_hook_loop, daemon=True).start()

    def _screenshot_hook_loop(self) -> None:
        try:
            user32 = ctypes.windll.user32
            kernel32 = ctypes.windll.kernel32
        except Exception:
            return

        class KeyboardHookStruct(ctypes.Structure):
            _fields_ = [
                ("vkCode", wintypes.DWORD),
                ("scanCode", wintypes.DWORD),
                ("flags", wintypes.DWORD),
                ("time", wintypes.DWORD),
                ("dwExtraInfo", ctypes.c_void_p),
            ]

        hook_type = ctypes.WINFUNCTYPE(
            ctypes.c_ssize_t, ctypes.c_int, wintypes.WPARAM, wintypes.LPARAM
        )
        hwnd = self._hwnd

        def is_down(vk: int) -> bool:
            return bool(user32.GetAsyncKeyState(vk) & 0x8000)

        def callback(n_code, w_param, l_param):
            try:
                if n_code >= 0 and w_param in (WM_KEYDOWN, WM_SYSKEYDOWN):
                    info = ctypes.cast(
                        l_param, ctypes.POINTER(KeyboardHookStruct)
                    ).contents
                    if (
                        info.vkCode == VK_SNAPSHOT
                        or (
                            (
                                (info.vkCode == VK_S and is_down(VK_SHIFT))
                                or info.vkCode == VK_C
                            )
                            and (is_down(VK_LWIN) or is_down(VK_RWIN))
                        )
                    ):
                        # Fn 一般由键盘固件处理，Windows 通常只能看到
                        # Win+Shift+S、Win+C 或 PrintScreen；这里按实际键码判断。
                        now = time.monotonic()
                        if now - self._hotkey_last > 0.8:
                            self._hotkey_last = now
                            # 在键盘钩子里先隐藏，抢在系统处理截图快捷键之前。
                            if hwnd and not user32.IsIconic(hwnd):
                                user32.ShowWindow(hwnd, 0)
                            if self._hud_hwnd and user32.IsWindowVisible(self._hud_hwnd):
                                self._hud_was_visible = True
                                user32.ShowWindow(self._hud_hwnd, 0)
                            self._ui_queue.put(("screenshot_hotkey",))
            except Exception:
                pass
            return user32.CallNextHookEx(None, n_code, w_param, l_param)

        self._hook_proc = hook_type(callback)
        kernel32.GetModuleHandleW.restype = wintypes.HMODULE
        user32.SetWindowsHookExW.restype = wintypes.HHOOK
        user32.SetWindowsHookExW.argtypes = [
            ctypes.c_int, hook_type, wintypes.HINSTANCE, wintypes.DWORD,
        ]
        try:
            handle = user32.SetWindowsHookExW(
                WH_KEYBOARD_LL, self._hook_proc, kernel32.GetModuleHandleW(None), 0
            )
        except Exception:
            handle = None
        if not handle:
            self._hook_proc = None
            return
        self._hook_handle = handle
        self._hook_thread_id = kernel32.GetCurrentThreadId()
        message = wintypes.MSG()
        while user32.GetMessageW(ctypes.byref(message), None, 0, 0) > 0:
            user32.TranslateMessage(ctypes.byref(message))
            user32.DispatchMessageW(ctypes.byref(message))
        try:
            user32.UnhookWindowsHookEx(handle)
        except Exception:
            pass
        self._hook_handle = None

    def _stop_screenshot_hook(self) -> None:
        try:
            if self._hook_handle:
                ctypes.windll.user32.UnhookWindowsHookEx(self._hook_handle)
                self._hook_handle = None
            if self._hook_thread_id:
                ctypes.windll.user32.PostThreadMessageW(
                    self._hook_thread_id, WM_QUIT, 0, 0
                )
                self._hook_thread_id = 0
        except Exception:
            pass

    def _enter_screenshot_mode(self) -> None:
        if self._closing:
            return
        if self._screenshot_hidden:
            self._reset_screenshot_watch()
            return
        try:
            state = self.state()
            if state == "iconic":
                return
            self._screenshot_hidden = True
            # 键盘钩子已经用 ShowWindow 抢先隐藏时，Tk 状态可能已经是 withdrawn。
            if state != "withdrawn":
                self.withdraw()
        except tk.TclError:
            self._screenshot_hidden = False
            return
        if self.hud and self.hud.winfo_exists():
            try:
                if self.hud.state() != "withdrawn":
                    self._hud_was_visible = True
                    self.hud.withdraw()
            except tk.TclError:
                pass
        self._reset_screenshot_watch()
        self.after(250, self._poll_screenshot_done)

    def _reset_screenshot_watch(self) -> None:
        self._screenshot_deadline = time.monotonic() + SCREENSHOT_HIDE_SECONDS
        try:
            self._clipboard_seq = ctypes.windll.user32.GetClipboardSequenceNumber()
        except Exception:
            self._clipboard_seq = 0

    def _poll_screenshot_done(self) -> None:
        if not self._screenshot_hidden or self._closing:
            return
        try:
            sequence = ctypes.windll.user32.GetClipboardSequenceNumber()
        except Exception:
            sequence = self._clipboard_seq
        if sequence != self._clipboard_seq or time.monotonic() >= self._screenshot_deadline:
            self._leave_screenshot_mode()
            return
        self.after(250, self._poll_screenshot_done)

    def _leave_screenshot_mode(self) -> None:
        if not self._screenshot_hidden:
            return
        self._screenshot_hidden = False
        try:
            self.deiconify()
            self.lift()
            self.attributes("-topmost", bool(self.topmost))
        except tk.TclError:
            pass
        if self._hud_was_visible and self.hud and self.hud.winfo_exists():
            try:
                self.hud.deiconify()
                self.hud.attributes("-topmost", True)
            except tk.TclError:
                pass
        self._hud_was_visible = False

    # -- 状态显示 -----------------------------------------------------------

    def _mode_text(self) -> str:
        if self.mode == "vision":
            return f"数学 OCR · {self.model}"
        if self.mode == "ocr":
            return f"OCR 文字 · {self.model}"
        if self.vision_supported is True:
            return f"数学 OCR · {self.model}"
        if self.vision_supported is False:
            return f"OCR 文字 · {self.model}"
        if not is_ollama_base(self.base_url) and looks_like_vision_model(self.model):
            return f"数学 OCR · {self.model}"
        return f"自动 · {self.model}"

    def _refresh_mode_text(self) -> None:
        self.mode_badge.configure(text=self._mode_text())
        self.subtitle.configure(text=f"自动监听新截图 · {self.model}")

    def _set_state(self, text: str, color: str = MUTED) -> None:
        self.status_dot.configure(fg=color)
        self.status_text.configure(text=text)

    def _set_stage(self, text: str, color: str = MUTED) -> None:
        self.stage_label.configure(text=text, fg=color)

    def _refresh_counter(self) -> None:
        text = f"已分析 {self.analyzed} 张"
        if self._pending:
            text += f" · 排队 {len(self._pending)}"
        self.count_label.configure(text=text)

    def _set_busy_buttons(self, busy: bool) -> None:
        self.stop_button.state(["!disabled"] if busy else ["disabled"])
        if busy or not self.last_image:
            self.reanalyze_button.state(["disabled"])
        else:
            self.reanalyze_button.state(["!disabled"])

    # -- 置顶 ---------------------------------------------------------------

    def toggle_topmost(self) -> None:
        self.topmost = not self.topmost
        self._apply_topmost()
        self.cfg["topmost"] = self.topmost
        save_config(self.cfg)

    def _apply_topmost(self) -> None:
        try:
            self.attributes("-topmost", bool(self.topmost))
        except tk.TclError:
            pass
        if self.topmost:
            self.pin_button.configure(text="置顶：开", style="Accent.TButton")
        else:
            self.pin_button.configure(text="置顶：关", style="TButton")

    # -- 监听 ---------------------------------------------------------------

    def _list_images(self, include_extra: bool = True) -> list[Path]:
        files: list[Path] = []
        try:
            files.extend(
                p for p in self.folder.iterdir()
                if p.is_file() and p.suffix.lower() in IMAGE_EXTS
            )
        except OSError as exc:
            message = f"无法读取监听目录：{exc}"
            if message != self._folder_error:
                self._folder_error = message
                self._ui_queue.put(("folder_error", message))
        else:
            if self._folder_error:
                self._folder_error = ""
                self._ui_queue.put(("folder_ok",))

        if include_extra:
            try:
                if EXTRA_FOLDER.is_dir():
                    files.extend(
                        p for p in EXTRA_FOLDER.iterdir()
                        if p.is_file() and p.suffix.lower() in EXTRA_EXTS
                    )
            except OSError:
                pass
        return files

    def _is_extra_path(self, path: Path) -> bool:
        try:
            return path.parent.resolve() == EXTRA_FOLDER.resolve()
        except (OSError, ValueError):
            return False

    def _temp_images(self) -> list[Path]:
        try:
            return [
                p for p in TEMP_DIR.iterdir()
                if p.is_file() and p.suffix.lower() in IMAGE_EXTS
            ]
        except OSError:
            return []

    def _is_temp_path(self, path: Path) -> bool:
        try:
            return path.resolve().is_relative_to(TEMP_DIR.resolve())
        except (OSError, ValueError):
            return False

    def _unique_temp_destination(self, name: str) -> Path:
        destination = TEMP_DIR / name
        if not destination.exists():
            return destination
        stem = Path(name).stem
        suffix = Path(name).suffix
        for counter in range(1, 10000):
            candidate = TEMP_DIR / f"{stem} ({counter}){suffix}"
            if not candidate.exists():
                return candidate
        return TEMP_DIR / f"{stem}_{int(time.time())}{suffix}"

    def _archive_image(self, path: Path | None) -> tuple[Path | None, str]:
        """把分析完成的截图移到 temp，返回新路径和错误信息。"""
        if path is None:
            return None, ""
        if self._is_temp_path(path):
            return path, ""
        if not path.exists():
            return None, "文件已不存在"
        try:
            TEMP_DIR.mkdir(parents=True, exist_ok=True)
            destination = self._unique_temp_destination(path.name)
            shutil.move(str(path), str(destination))
        except OSError as exc:
            return None, str(exc)
        self._seen.pop(path, None)
        self._probe.pop(path, None)
        return destination, ""

    def _cache_files(self) -> list[Path]:
        try:
            return [p for p in TEMP_DIR.rglob("*") if p.is_file()]
        except OSError:
            return []

    def _clear_cache_files(self) -> tuple[int, int, int]:
        removed = 0
        freed = 0
        errors = 0
        if not TEMP_DIR.exists():
            return removed, freed, errors
        for child in list(TEMP_DIR.iterdir()):
            try:
                if child.is_dir():
                    size = sum(p.stat().st_size for p in child.rglob("*") if p.is_file())
                    shutil.rmtree(child)
                else:
                    size = child.stat().st_size
                    child.unlink()
                removed += 1
                freed += size
            except OSError:
                errors += 1
        return removed, freed, errors

    def _after_cache_cleared(self) -> None:
        self.ocr_cache.clear()
        current = self.last_image
        if current and self._is_temp_path(current) and not current.exists():
            self.last_image = None
            self.current_image = None
            self._thumb_image = None
            self.thumb.configure(image="", text="暂无截图")
            self.file_label.configure(text="等待新的截图…")
            self.meta_label.configure(text="缓存已清理")
            self.reanalyze_button.state(["disabled"])
            self._set_stage("● 缓存已清理", MUTED)

    def _reset_baseline(self, show_newest: bool = False) -> None:
        self._probe.clear()
        self._seen = {}
        files = self._list_images()
        for path in files:
            try:
                stat = path.stat()
            except OSError:
                continue
            self._seen[path] = (stat.st_size, stat.st_mtime_ns)
        if show_newest and not self.busy:
            candidates = [
                p for p in files if not self._is_extra_path(p)
            ] + self._temp_images()
            if candidates:
                try:
                    newest = max(candidates, key=lambda p: p.stat().st_mtime_ns)
                except OSError:
                    newest = candidates[0]
                self._show_current(newest, from_startup=True)

    def _poll_folder(self) -> None:
        if self._closing:
            return
        if self.watching:
            self._scan_once()
        self.after(POLL_MS, self._poll_folder)

    def _scan_once(self) -> None:
        images = self._list_images()
        if not images:
            return
        alive = set(images)
        for stale in [p for p in self._probe if p not in alive]:
            self._probe.pop(stale, None)

        fresh: list[Path] = []
        for path in images:
            try:
                stat = path.stat()
            except OSError:
                continue
            signature = (stat.st_size, stat.st_mtime_ns)
            if self._seen.get(path) == signature:
                continue
            if stat.st_size == 0:
                continue
            previous = self._probe.get(path)
            if previous and previous[0] == signature:
                count = previous[1] + 1
            else:
                count = 1
            if count >= 2:
                self._probe.pop(path, None)
                self._seen[path] = signature
                fresh.append(path)
            else:
                self._probe[path] = (signature, count)

        if fresh and self._screenshot_hidden:
            self._leave_screenshot_mode()
        for path in sorted(fresh, key=lambda p: self._seen.get(p, (0, 0))[1]):
            self._enqueue(path)

    def _enqueue(self, path: Path) -> None:
        try:
            if path.stat().st_size == 0:
                return
        except OSError:
            return
        if self.busy:
            if len(self._pending) >= 2:
                dropped = self._pending.popleft()
                self._ui_queue.put(("notice", f"截图来得太快，已跳过 {dropped.name}"))
            self._pending.append(path)
            self._refresh_counter()
            return
        self._pending.append(path)
        self._maybe_start_next()

    def _maybe_start_next(self) -> None:
        if self.busy or self._closing or not self._pending:
            return
        path = self._pending.popleft()
        self.busy = True
        self.current_image = path
        self.last_image = path
        self.answer_text = ""
        self.started_at = time.monotonic()
        self.stage_kind = "prepare"
        self._cancel.clear()
        self._refresh_counter()

        prompt = self.prompt_var.get().strip() or prompt_for_type(self.answer_type)
        context = {
            "base_url": self.base_url,
            "api_key": self.api_key,
            "deepseek_no_think": self.deepseek_no_think,
            "model": self.model,
            "mode": self.mode,
            "vision": self.vision_supported,
            "prompt": prompt,
            "answer_type": self.answer_type,
        }
        self._ui_queue.put(("started", path))
        threading.Thread(target=self._worker, args=(path, context), daemon=True).start()

    # -- 后台任务 -----------------------------------------------------------

    def _detect_async(self) -> None:
        base_url = self.base_url
        model = self.model

        def work() -> None:
            if not is_ollama_base(base_url):
                self._ui_queue.put(("caps_error",))
                return
            try:
                vision, capabilities = detect_vision(base_url, model)
                self._ui_queue.put(("caps", vision, capabilities))
            except Exception:
                self._ui_queue.put(("caps_error",))

        threading.Thread(target=work, daemon=True).start()

    def _resolve_mode(self, context: dict) -> str:
        if context["mode"] == "ocr":
            return "ocr"
        if context["mode"] == "vision":
            return "vision"
        if not is_ollama_base(context["base_url"]):
            return "vision" if looks_like_vision_model(context["model"]) else "ocr"
        vision = context["vision"]
        if vision is None:
            try:
                vision, capabilities = detect_vision(context["base_url"], context["model"])
                context["vision"] = vision
                self._ui_queue.put(("caps", vision, capabilities))
            except Exception:
                context["vision"] = False
                vision = False
        return "vision" if vision else "ocr"

    def _ocr_cached(self, path: Path) -> str:
        try:
            stat = path.stat()
        except OSError as exc:
            raise AnalysisError(f"无法读取截图：{exc}") from exc
        key = (str(path), stat.st_size, stat.st_mtime_ns)
        cached = self.ocr_cache.get(key)
        if cached is not None:
            return cached
        result = run_ocr(path)
        if not result.get("ok"):
            raise AnalysisError(result.get("error") or "OCR 识别失败。")
        text = result.get("text") or ""
        if len(self.ocr_cache) > 12:
            self.ocr_cache.pop(next(iter(self.ocr_cache)), None)
        self.ocr_cache[key] = text
        return text

    def _bank_entries(self) -> list[dict]:
        try:
            mtime = self.bank_path.stat().st_mtime_ns
        except OSError:
            return []
        if self._bank_cache and self._bank_cache[0] == mtime:
            return self._bank_cache[1]
        entries = load_question_bank(self.bank_path)
        self._bank_cache = (mtime, entries)
        return entries

    def _bank_matches(self, ocr_text: str) -> tuple[dict[str, str], bool]:
        entries = self._bank_entries()
        if not entries:
            return {}, False
        matches = match_question_bank(entries, ocr_text)
        numbers = extract_question_numbers(ocr_text)
        all_matched = bool(matches) and bool(numbers) and all(
            number in matches for number in numbers
        )
        return matches, all_matched

    def _worker(self, path: Path, context: dict) -> None:
        try:
            mode = self._resolve_mode(context)
            ocr_text = ""
            if mode == "vision":
                self._ui_queue.put(("stage", "upload", "正在用数学 OCR 识别公式…"))
                messages = self._build_math_ocr_messages(path)
                try:
                    transcription, _thinking, _truncated = self._call_model(messages, context)
                except AnalysisError as exc:
                    if self._looks_like_no_vision(str(exc)):
                        context["vision"] = False
                        self._ui_queue.put(("caps", False, []))
                        self._ui_queue.put(("stage", "ocr", "正在用 Windows OCR 识别文字…"))
                        ocr_text = self._ocr_for_prompt(path)
                    else:
                        raise
                else:
                    transcription = transcription.strip()
                    if transcription:
                        ocr_text = transcription
                        self._ui_queue.put(("stage", "ocr", "数学公式转写完成…"))
                    else:
                        self._ui_queue.put(("stage", "ocr", "数学 OCR 结果为空，改用 Windows OCR…"))
                        ocr_text = self._ocr_for_prompt(path)
            else:
                self._ui_queue.put(("stage", "ocr", "正在用 Windows OCR 识别文字…"))
                ocr_text = self._ocr_for_prompt(path)

            answer, thinking, truncated, bank_count, total_count = self._answer_from_text(
                path, ocr_text, context
            )
            content_missing = not answer.strip() and bool(thinking.strip())
            if content_missing:
                answer = thinking
            if self._cancel.is_set():
                raise Cancelled()
            elapsed = time.monotonic() - self.started_at
            self._ui_queue.put(
                ("done", answer, elapsed, content_missing, truncated, bank_count, total_count)
            )
        except Cancelled:
            self._ui_queue.put(("cancelled",))
        except AnalysisError as exc:
            self._ui_queue.put(("error", str(exc)))
        except Exception as exc:  # 兜底，避免线程静默失败
            self._ui_queue.put(("error", f"处理截图时出错：{exc}"))
        finally:
            self._ui_queue.put(("finished",))

    def _answer_from_text(
        self, path: Path, ocr_text: str, context: dict
    ) -> tuple[str, str, bool, int, int]:
        bank_count = 0
        total_count = 0
        if context["answer_type"] != "answer":
            messages = self._build_ocr_messages(
                path, ocr_text, context["prompt"], context["answer_type"]
            )
            self._ui_queue.put(("stage", "model", "模型生成中…"))
            answer, thinking, truncated = self._call_model(messages, context)
            return answer, thinking, truncated, bank_count, total_count

        matches, _all_matched = self._bank_matches(ocr_text)
        numbers = extract_question_numbers(ocr_text)
        missing = [number for number in numbers if number not in matches]
        bank_count = sum(1 for number in numbers if number in matches)
        total_count = len(numbers)
        if numbers and not missing:
            answer = format_bank_answers(matches)
            thinking = ""
            truncated = False
            self._ui_queue.put(
                ("stage", "bank", f"题库命中 {bank_count}/{total_count} 题…")
            )
            return answer, thinking, truncated, bank_count, total_count

        if matches:
            self._ui_queue.put((
                "stage", "bank",
                f"题库命中 {bank_count} 题，模型补答 {len(missing)} 题…",
            ))
        else:
            self._ui_queue.put(("stage", "model", "模型生成中…"))

        blocks = {
            block["number"]: block
            for block in extract_question_blocks(ocr_text)
        }
        missing_text = ""
        if numbers and matches:
            missing_text = "\n\n".join(
                "\n".join(blocks[number]["lines"])
                for number in missing
                if number in blocks
            )
        model_text = missing_text or ocr_text
        model_prompt = context["prompt"].rstrip()
        if numbers:
            model_prompt += (
                "\n只回答下面列出的题目，严格按“题号. 答案”逐行输出；"
                "不要回答未列出的题目，不要解释。"
            )
        messages = self._build_ocr_messages(
            path, model_text, model_prompt, context["answer_type"]
        )
        answer, thinking, truncated = self._call_model(messages, context)
        if numbers:
            answer = combine_question_answers(matches, answer, numbers)
        elif matches:
            answer = apply_bank_overrides(answer, matches)
        return answer, thinking, truncated, bank_count, total_count

    def _ocr_for_prompt(self, path: Path) -> str:
        text = self._ocr_cached(path)
        if not text.strip():
            return "（OCR 没有从这张截图里识别到文字。截图可能是纯图片、图表或图形界面。）"
        return text

    @staticmethod
    def _looks_like_no_vision(message: str) -> bool:
        text = message.lower()
        return "image" in text and any(word in text for word in ("support", "vision", "multimodal"))

    def _build_ocr_messages(
        self, path: Path, ocr_text: str, prompt: str, answer_type: str
    ) -> list[dict]:
        if len(ocr_text) > MAX_OCR_CHARS:
            ocr_text = ocr_text[:MAX_OCR_CHARS] + "\n…（文字过长，已截断）"
        system = SYSTEM_PROMPTS_OCR.get(answer_type, SYSTEM_PROMPTS_OCR[DEFAULT_ANSWER_TYPE])
        if answer_type == "summary":
            user = f"【页面文字（OCR）】\n{ocr_text}\n\n【任务】\n{prompt}"
        else:
            user = (
                f"截图文件：{path.name}\n\n"
                f"【截图文字（OCR，可能有识别错误）】\n{ocr_text}\n\n"
                f"【任务】\n{prompt}"
            )
        return [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ]

    def _build_vision_messages(self, path: Path, prompt: str, answer_type: str) -> list[dict]:
        data = base64.b64encode(path.read_bytes()).decode("ascii")
        system = SYSTEM_PROMPTS_VISION.get(answer_type, SYSTEM_PROMPTS_VISION[DEFAULT_ANSWER_TYPE])
        user_text = f"任务：{prompt}" if answer_type == "summary" else f"截图文件：{path.name}\n\n任务：{prompt}"
        user_content = [
            {"type": "text", "text": user_text},
            {"type": "image_url", "image_url": {"url": f"data:{mime_for(path)};base64,{data}"}},
        ]
        return [
            {"role": "system", "content": system},
            {"role": "user", "content": user_content},
        ]

    def _build_math_ocr_messages(self, path: Path) -> list[dict]:
        data = base64.b64encode(path.read_bytes()).decode("ascii")
        return [
            {"role": "system", "content": MATH_OCR_PROMPT},
            {
                "role": "user",
                "content": [
                    {"type": "text", "text": "请转写这张数学题截图的全部题目和公式。"},
                    {
                        "type": "image_url",
                        "image_url": {"url": f"data:{mime_for(path)};base64,{data}"},
                    },
                ],
            },
        ]

    def _call_model(self, messages: list[dict], context: dict):
        """Ollama 本地服务优先用原生接口，其他 OpenAI 兼容服务直接走 /v1。"""
        if self.native_available and is_ollama_base(context["base_url"]):
            try:
                return self._call_ollama(messages, context)
            except NativeUnavailable:
                self.native_available = False
        return self._call_openai(messages, context)

    @staticmethod
    def _to_native_messages(messages: list[dict]) -> list[dict]:
        native = []
        for message in messages:
            content = message.get("content")
            if isinstance(content, str):
                native.append({"role": message["role"], "content": content})
                continue
            texts: list[str] = []
            images: list[str] = []
            for part in content or []:
                if part.get("type") == "text":
                    texts.append(part.get("text") or "")
                elif part.get("type") == "image_url":
                    url = ((part.get("image_url") or {}).get("url") or "")
                    if url.startswith("data:") and "," in url:
                        images.append(url.split(",", 1)[1])
            item = {"role": message["role"], "content": "\n".join(texts)}
            if images:
                item["images"] = images
            native.append(item)
        return native

    def _call_ollama(self, messages: list[dict], context: dict):
        temperature = 0.0 if context.get("answer_type") == "answer" else 0.2
        payload = {
            "model": context["model"],
            "messages": self._to_native_messages(messages),
            "stream": True,
            "think": False,
            "options": {
                "temperature": temperature,
                "num_predict": MAX_TOKENS,
            },
        }
        body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        url = api_root(context["base_url"]) + "/api/chat"

        try:
            connection, response = open_chat_connection(
                url, body, accept="application/x-ndjson",
                api_key=context.get("api_key", ""),
            )
        except (OSError, http.client.HTTPException, ValueError) as exc:
            raise AnalysisError(
                f"无法连接模型服务：{exc}\n"
                f"请确认 Ollama 正在运行，接口地址是 {context['base_url']}。"
            ) from exc

        with self._connection_lock:
            self._connection = connection
        try:
            if response.status in (404, 405):
                raise NativeUnavailable()
            if response.status >= 400:
                raw = response.read().decode("utf-8", "replace")
                raise AnalysisError(self._http_error_text(response.status, raw))

            parts: list[str] = []
            thinking_parts: list[str] = []
            truncated = False
            for raw_line in response:
                if self._cancel.is_set():
                    raise Cancelled()
                line = raw_line.decode("utf-8", "replace").strip()
                if not line:
                    continue
                try:
                    chunk = json.loads(line)
                except ValueError:
                    continue
                if "error" in chunk:
                    raise AnalysisError(self._object_error_text(chunk["error"]))
                message = chunk.get("message") or {}
                piece = message.get("content") or ""
                if piece:
                    parts.append(piece)
                    self._ui_queue.put(("delta", piece))
                thought = message.get("thinking") or ""
                if thought:
                    thinking_parts.append(thought)
                    self._ui_queue.put(("thinking", thought))
                if chunk.get("done"):
                    truncated = chunk.get("done_reason") == "length"
                    break
            if self._cancel.is_set():
                raise Cancelled()
            return "".join(parts), "".join(thinking_parts), truncated
        except (TimeoutError, socket.timeout) as exc:
            if self._cancel.is_set():
                raise Cancelled() from exc
            raise AnalysisError("等待模型响应超时。") from exc
        except (AnalysisError, NativeUnavailable):
            raise
        except (OSError, http.client.HTTPException) as exc:
            if self._cancel.is_set():
                raise Cancelled() from exc
            raise AnalysisError(f"读取模型响应时连接中断：{exc}") from exc
        finally:
            with self._connection_lock:
                if self._connection is connection:
                    self._connection = None
            try:
                response.close()
            except Exception:
                pass
            try:
                connection.close()
            except Exception:
                pass

    @staticmethod
    def _thinking_unsupported(status: int, raw: str) -> bool:
        if status not in (400, 422):
            return False
        text = raw.lower()
        if "thinking" not in text:
            return False
        return any(
            word in text
            for word in (
                "unknown", "unrecognized", "unsupported", "unexpected",
                "extra", "invalid", "not permitted", "not supported",
            )
        )

    def _call_openai(self, messages: list[dict], context: dict):
        temperature = 0.0 if context.get("answer_type") == "answer" else 0.2
        payload = {
            "model": context["model"],
            "messages": messages,
            "temperature": temperature,
            "max_tokens": MAX_TOKENS,
            "stream": True,
        }
        if context.get("deepseek_no_think") and not is_ollama_base(context["base_url"]):
            payload["thinking"] = {"type": "disabled"}
        body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        url = chat_url(context["base_url"])
        thinking_added = "thinking" in payload
        connection = None
        response = None

        for attempt in range(2):
            try:
                connection, response = open_chat_connection(
                    url, body, api_key=context.get("api_key", "")
                )
            except (OSError, http.client.HTTPException, ValueError) as exc:
                raise AnalysisError(
                    f"无法连接模型服务：{exc}\n"
                    f"请确认模型服务和网络可用，接口地址是 {url}。"
                ) from exc

            if response.status < 400:
                break

            raw = response.read().decode("utf-8", "replace")
            try:
                response.close()
            except Exception:
                pass
            try:
                connection.close()
            except Exception:
                pass
            if (
                attempt == 0
                and thinking_added
                and self._thinking_unsupported(response.status, raw)
            ):
                payload.pop("thinking", None)
                body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
                thinking_added = False
                connection = None
                response = None
                continue
            raise AnalysisError(self._http_error_text(response.status, raw))

        if connection is None or response is None:
            raise AnalysisError("模型服务没有返回响应。")

        with self._connection_lock:
            self._connection = connection
        try:
            content_type = (response.headers.get("Content-Type") or "").lower()
            if "text/event-stream" not in content_type:
                return self._read_plain_response(response)

            parts: list[str] = []
            thinking_parts: list[str] = []
            truncated = False
            for raw_line in response:
                if self._cancel.is_set():
                    raise Cancelled()
                line = raw_line.decode("utf-8", "replace").strip()
                if not line or not line.startswith("data:"):
                    continue
                data = line[5:].strip()
                if data == "[DONE]":
                    break
                try:
                    chunk = json.loads(data)
                except ValueError:
                    continue
                if "error" in chunk:
                    raise AnalysisError(self._object_error_text(chunk["error"]))
                choices = chunk.get("choices") or []
                if not choices:
                    continue
                choice = choices[0]
                if choice.get("finish_reason") == "length":
                    truncated = True
                delta = choice.get("delta") or choice.get("message") or {}
                piece = delta.get("content") or ""
                if piece:
                    parts.append(piece)
                    self._ui_queue.put(("delta", piece))
                thought = delta.get("reasoning_content") or delta.get("reasoning") or ""
                if thought:
                    thinking_parts.append(thought)
                    self._ui_queue.put(("thinking", thought))
            if self._cancel.is_set():
                raise Cancelled()
            return "".join(parts), "".join(thinking_parts), truncated
        except (TimeoutError, socket.timeout) as exc:
            if self._cancel.is_set():
                raise Cancelled() from exc
            raise AnalysisError("等待模型响应超时。如果截图文字很多，可以缩短问题后重试。") from exc
        except AnalysisError:
            raise
        except (OSError, http.client.HTTPException) as exc:
            if self._cancel.is_set():
                raise Cancelled() from exc
            raise AnalysisError(f"读取模型响应时连接中断：{exc}") from exc
        finally:
            with self._connection_lock:
                if self._connection is connection:
                    self._connection = None
            try:
                response.close()
            except Exception:
                pass
            try:
                connection.close()
            except Exception:
                pass

    def _read_plain_response(self, response):
        raw = response.read()
        try:
            data = json.loads(raw.decode("utf-8", "replace"))
        except ValueError as exc:
            raise AnalysisError("模型返回了无法解析的内容。") from exc
        if "error" in data:
            raise AnalysisError(self._object_error_text(data["error"]))
        choices = data.get("choices") or []
        if not choices:
            return "", "", False
        message = choices[0].get("message") or {}
        content = message.get("content") or ""
        thinking = message.get("reasoning_content") or message.get("reasoning") or ""
        if content:
            self._ui_queue.put(("delta", content))
        truncated = choices[0].get("finish_reason") == "length"
        return content, thinking, truncated

    @staticmethod
    def _object_error_text(error) -> str:
        if isinstance(error, dict):
            return str(error.get("message") or error.get("error") or error)
        return str(error)

    def _http_error_text(self, status: int, body: str) -> str:
        message = ""
        try:
            data = json.loads(body)
            message = self._object_error_text(data.get("error") or data.get("message") or "")
        except (ValueError, AttributeError):
            message = body.strip()[:600]
        if not message:
            message = "未知错误"
        hint = ""
        if status == 404:
            hint = "\n提示：检查设置里的模型名称和接口地址（应类似 http://127.0.0.1:11434/v1）。"
        elif status in (401, 403):
            hint = "\n提示：检查设置里的 API Key 是否正确；官方 API 需要填写有效的 API Key。"
        elif status == 400 and "image" in message.lower():
            hint = "\n提示：当前模型可能不支持图片输入，可在设置里把模式改成“OCR 文字”。"
        return f"模型请求失败（HTTP {status}）：{message}{hint}"

    # -- 界面事件 -----------------------------------------------------------

    def _pump(self) -> None:
        try:
            while True:
                event = self._ui_queue.get_nowait()
                self._handle_event(event)
        except queue.Empty:
            pass
        if not self._closing:
            if self.busy and not self._clearing:
                self._tick()
            self.after(80, self._pump)

    def _handle_event(self, event: tuple) -> None:
        kind = event[0]
        if self._clearing and kind in {
            "started", "stage", "delta", "thinking", "done", "error", "cancelled",
        }:
            return
        if kind == "screenshot_hotkey":
            self._enter_screenshot_mode()
        elif kind == "started":
            path: Path = event[1]
            self._show_current(path)
            self._set_answer_placeholder("")
            self._set_stage("● 准备分析…", ACCENT)
            self._set_state("生成中…", ACCENT)
            self.stage_kind = "prepare"
            self._set_busy_buttons(True)
            self._refresh_counter()
        elif kind == "stage":
            stage = event[1]
            text = event[2]
            self.started_at = self.started_at or time.monotonic()
            self._set_stage("● " + text, ACCENT)
            self._set_state("生成中…", ACCENT)
            self.stage_kind = stage
        elif kind == "delta":
            self._append_answer(event[1])
        elif kind == "thinking":
            if self.stage_kind != "model":
                self._set_stage("● 模型思考中…", ACCENT)
            self.stage_kind = "model"
        elif kind == "done":
            answer, elapsed, missing, truncated = event[1], event[2], event[3], event[4]
            bank_count = event[5] if len(event) > 5 else 0
            total_count = event[6] if len(event) > 6 else bank_count
            source = self.current_image
            archived, archive_error = self._archive_image(source) if source else (None, "")
            self.busy = False
            self.current_image = None
            self.answer_text = answer
            self._render_answer(answer)
            self._set_plugin_answers(answer)
            self._refresh_hud()
            if missing:
                self._append_note("（模型没有给出正式回答，以上是它的思考过程。）")
            if truncated:
                self._append_note("（回答达到长度上限，可能被截断。）")
            if archived:
                self.last_image = archived
            elif source:
                self.last_image = source
            suffix = ""
            if archive_error:
                suffix = "（缓存移动失败）"
            elif archived and source and archived != source:
                suffix = " · 已移入缓存"
                self.file_label.configure(text=shorten(archived.name, 40))
                meta = str(self.meta_label.cget("text"))
                if "已移入缓存" not in meta:
                    self.meta_label.configure(text=meta + " · 已移入缓存")
            if bank_count:
                suffix += f" · 题库命中 {bank_count}/{total_count} 题"
                if total_count > bank_count:
                    suffix += f" · 模型补答 {total_count - bank_count} 题"
            elif total_count:
                suffix += f" · 模型作答 {total_count} 题"
            self._set_stage(f"● 已完成 · {elapsed:.1f}s{suffix}", WARN if archive_error else OK)
            self._set_state("监听中", OK)
            self.analyzed += 1
            self._set_busy_buttons(False)
            self._refresh_counter()
        elif kind == "error":
            self.busy = False
            self.current_image = None
            self.answer_text = ""
            self._render_error(event[1])
            self._set_stage("● 出错", ERR)
            self._set_state("出错", ERR)
            self._set_busy_buttons(False)
            self._refresh_counter()
        elif kind == "cancelled":
            self.busy = False
            self.current_image = None
            self._append_note("（已停止生成。）")
            self._set_stage("● 已停止", MUTED)
            self._set_state("监听中", OK)
            self._set_busy_buttons(False)
            self._refresh_counter()
        elif kind == "finished":
            if self._clearing:
                self.busy = False
                self._clearing = False
                self._set_busy_buttons(False)
                self._refresh_counter()
                self._maybe_start_next()
                return
            self.busy = False
            self._set_busy_buttons(False)
            if not self._pending:
                self.current_image = None
            self._refresh_counter()
            self._maybe_start_next()
        elif kind == "caps":
            vision = event[1]
            if self.mode == "auto" and vision is not None:
                self.vision_supported = vision
            self._refresh_mode_text()
        elif kind == "caps_error":
            self._refresh_mode_text()
        elif kind == "notice":
            self._set_stage("● " + event[1], WARN)
        elif kind == "folder_error":
            self._set_state("目录不可用", ERR)
            self._set_stage("● " + event[1], ERR)
            self.folder_label.configure(text=shorten(str(self.folder), 36), fg=ERR)
        elif kind == "folder_ok":
            self.folder_label.configure(fg=MUTED)
            if not self.busy:
                self._set_state("监听中" if self.watching else "已暂停", OK if self.watching else WARN)

    def _tick(self) -> None:
        elapsed = time.monotonic() - self.started_at
        if self.stage_kind == "ocr":
            self._set_stage(f"● Windows OCR 识别中… {elapsed:.1f}s", ACCENT)
        elif self.stage_kind == "upload":
            self._set_stage(f"● 正在上传截图… {elapsed:.1f}s", ACCENT)
        elif self.stage_kind == "model":
            self._set_stage(f"● 模型生成中… {elapsed:.1f}s", ACCENT)
        else:
            self._set_stage(f"● 准备分析… {elapsed:.1f}s", ACCENT)
        self._set_state(f"生成中 {elapsed:.0f}s", ACCENT)

    # -- 回答文本 -----------------------------------------------------------

    def _set_answer_placeholder(self, text: str) -> None:
        self.text.configure(state="normal")
        self.text.delete("1.0", "end")
        if text:
            self.text.insert("1.0", text, "muted")
        self.text.configure(state="disabled")
        self.answer_text = ""
        self._answer_rendered = False

    def _append_answer(self, piece: str) -> None:
        at_bottom = self.text.yview()[1] >= 0.99
        self.text.configure(state="normal")
        self.text.insert("end", piece, "answer")
        self.text.configure(state="disabled")
        self.answer_text += piece
        if at_bottom:
            self.text.see("end")

    def _append_note(self, text: str) -> None:
        self.text.configure(state="normal")
        self.text.insert("end", "\n" + text, "muted")
        self.text.configure(state="disabled")
        self.text.see("end")

    def _render_error(self, message: str) -> None:
        self.text.configure(state="normal")
        self.text.delete("1.0", "end")
        self.text.insert("1.0", "没能得到回答\n\n", "error")
        self.text.insert("end", message, "error")
        self.text.configure(state="disabled")
        self.text.see("1.0")

    def _render_answer(self, raw: str) -> None:
        self.text.configure(state="normal")
        self.text.delete("1.0", "end")
        if not raw.strip():
            self.text.insert("1.0", "（模型没有返回内容）", "muted")
        else:
            position = 0
            for match in re.finditer(r"```([^\n`]*)\n(.*?)(?:```|$)", raw, re.S):
                self._insert_inline(raw[position:match.start()])
                code = match.group(2)
                if code.endswith("\n"):
                    code = code[:-1]
                self.text.insert("end", code + "\n", "code")
                position = match.end()
            self._insert_inline(raw[position:])
        self.text.configure(state="disabled")
        self.text.see("1.0")
        self.text.yview_moveto(0.0)
        self._answer_rendered = True

    def _insert_inline(self, text: str) -> None:
        if not text:
            return
        for part in re.split(r"(`[^`\n]+`)", text):
            if len(part) > 1 and part.startswith("`") and part.endswith("`"):
                self.text.insert("end", part[1:-1], "inline")
            else:
                for segment in re.split(r"(\*\*[^*\n]+\*\*)", part):
                    if len(segment) > 4 and segment.startswith("**") and segment.endswith("**"):
                        self.text.insert("end", segment[2:-2], "strong")
                    else:
                        self.text.insert("end", segment, "answer")

    def copy_answer(self) -> None:
        content = self.answer_text.strip()
        if not content and self._answer_rendered:
            content = self.text.get("1.0", "end").strip()
        if not content:
            self._set_stage("● 还没有可复制的回答", WARN)
            return
        self.clipboard_clear()
        self.clipboard_append(content)
        self.copy_button.configure(text="已复制")
        self.after(1400, lambda: self.copy_button.configure(text="复制"))

    # -- 截图预览 -----------------------------------------------------------

    def _show_current(self, path: Path, from_startup: bool = False) -> None:
        self.last_image = path
        self.current_image = path if self.busy else None
        self.file_label.configure(text=shorten(path.name, 40))
        try:
            stat = path.stat()
            stamp = time.strftime("%H:%M:%S", time.localtime(stat.st_mtime))
            info = f"{stamp} · {human_size(stat.st_size)}"
        except OSError:
            info = ""
        self._load_thumbnail(path, info)
        self.reanalyze_button.state(["!disabled"])
        if from_startup:
            self._set_stage("● 就绪，等待新的截图", MUTED)

    def _load_thumbnail(self, path: Path, info: str) -> None:
        try:
            image = tk.PhotoImage(file=str(path))
            width, height = image.width(), image.height()
            factor = max(1, math.ceil(max(width / 216, height / 136)))
            if factor > 1:
                image = image.subsample(factor, factor)
        except tk.TclError:
            self._thumb_image = None
            self.thumb.configure(image="", text="无法预览\n（点击打开原图）")
            self.meta_label.configure(text=info)
            return
        self._thumb_image = image
        self.thumb.configure(image=image, text="")
        if info:
            info = f"{info} · {width}×{height}"
        self.meta_label.configure(text=info)

    def open_current_image(self) -> None:
        path = self.current_image or self.last_image
        if not path or not path.exists():
            self._set_stage("● 没有可打开的截图", WARN)
            return
        try:
            os.startfile(str(path))
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"无法打开图片：{exc}", parent=self)

    def reanalyze(self) -> None:
        if self.busy:
            self._set_stage("● 正在生成，请稍候", WARN)
            return
        path = self.current_image or self.last_image
        if not path or not path.exists():
            self._set_stage("● 还没有可分析的截图", WARN)
            return
        self._enqueue(path)

    def cancel_current(self) -> None:
        if not self.busy or self._clearing:
            return
        self._cancel.set()
        self._abort_connection()
        self._set_stage("● 正在停止…", MUTED)
        self.stop_button.state(["disabled"])

    def clear_current_page(self) -> None:
        if self.busy:
            self._clearing = True
            self._cancel.set()
            self._abort_connection()
        self._pending.clear()
        self.last_image = None
        self.current_image = None
        self._thumb_image = None
        self.thumb.configure(image="", text="暂无截图")
        self.file_label.configure(text="等待新的截图…")
        self.meta_label.configure(text="把截图保存到监听目录即可自动分析")
        self._set_answer_placeholder(
            "等待新的截图…\n\n截图和回答已清空，保存新截图即可重新分析。"
        )
        self._set_plugin_answers("")
        self.stage_kind = "idle"
        self._set_stage("● 已清空", MUTED)
        self._set_state("监听中" if self.watching else "已暂停",
                        OK if self.watching else WARN)
        self._set_busy_buttons(False)
        self._refresh_counter()

    def _abort_connection(self) -> None:
        with self._connection_lock:
            connection = self._connection
            self._connection = None
        if connection is not None:
            try:
                connection.close()
            except Exception:
                pass

    def toggle_pause(self) -> None:
        self.watching = not self.watching
        self.pause_button.configure(text="继续" if not self.watching else "暂停")
        if self.watching:
            self._set_state("监听中", OK)
            self._set_stage("● 已恢复监听", OK)
        else:
            if self._pending:
                self._pending.clear()
                self._refresh_counter()
            self._set_state("已暂停", WARN)
            self._set_stage("● 已暂停，不会分析新截图", WARN)

    # -- 设置 ---------------------------------------------------------------

    def open_settings(self) -> None:
        if self.busy:
            messagebox.showinfo(APP_NAME, "模型正在回答，请等当前任务完成后再修改设置。", parent=self)
            return

        dialog = tk.Toplevel(self)
        dialog.title("设置")
        dialog.configure(bg=BG)
        dialog.transient(self)
        dialog.resizable(False, False)
        dialog.grab_set()

        width, height = 560, 735
        dialog.update_idletasks()
        x = self.winfo_rootx() + max(0, (self.winfo_width() - width) // 2)
        screen_h = self.winfo_screenheight()
        height = min(height, max(560, screen_h - 120))
        y = min(self.winfo_rooty() + 70, max(10, screen_h - height - 50))
        dialog.geometry(f"{width}x{height}+{x}+{y}")

        card = self._card(dialog)
        card.pack(fill="both", expand=True, padx=16, pady=16)
        card.columnconfigure(1, weight=1)

        folder_var = tk.StringVar(value=str(self.folder))
        base_var = tk.StringVar(value=self.base_url)
        api_key_var = tk.StringVar(value=self.api_key)
        no_think_var = tk.BooleanVar(value=self.deepseek_no_think)
        model_var = tk.StringVar(value=self.model)
        mode_var = tk.StringVar(value=MODE_LABELS[self.mode])
        type_var = tk.StringVar(value=ANSWER_TYPE_LABELS[self.answer_type])

        def add_row(row: int, label: str, widget) -> None:
            tk.Label(card, text=label, bg=CARD, fg=MUTED, font=(self.font_family, 9)).grid(
                row=row, column=0, sticky="w", padx=(16, 10), pady=(12, 0))
            widget.grid(row=row, column=1, columnspan=2, sticky="ew", padx=(0, 16), pady=(12, 0))

        folder_entry = ttk.Entry(card, textvariable=folder_var)
        tk.Label(card, text="监听目录", bg=CARD, fg=MUTED,
                 font=(self.font_family, 9)).grid(row=0, column=0, sticky="w", padx=(16, 10), pady=(12, 0))
        folder_entry.grid(row=0, column=1, sticky="ew", padx=(0, 6), pady=(12, 0))

        def browse() -> None:
            chosen = filedialog.askdirectory(parent=dialog, initialdir=str(self.folder),
                                             title="选择截图目录")
            if chosen:
                folder_var.set(chosen)

        ttk.Button(card, text="浏览", width=5, command=browse).grid(
            row=0, column=2, sticky="e", padx=(0, 16), pady=(12, 0))

        tk.Label(card, text="附加目录", bg=CARD, fg=MUTED,
                 font=(self.font_family, 9)).grid(
            row=1, column=0, sticky="w", padx=(16, 10), pady=(12, 0))
        tk.Label(
            card, text=f"{EXTRA_FOLDER}（仅 .jpeg → temp）",
            bg=CARD, fg=MUTED, font=(self.font_family, 8), anchor="w",
        ).grid(row=1, column=1, columnspan=2, sticky="w", padx=(0, 16), pady=(12, 0))

        add_row(2, "接口地址", ttk.Entry(card, textvariable=base_var))

        api_key_box = tk.Frame(card, bg=CARD)
        api_key_box.columnconfigure(0, weight=1)
        api_key_entry = ttk.Entry(api_key_box, textvariable=api_key_var, show="•")
        api_key_hint = tk.Label(
            api_key_box, text="（需要鉴权的 API 填写）", bg=CARD, fg=MUTED,
            font=(self.font_family, 8),
        )
        api_key_entry.grid(row=0, column=0, sticky="ew")
        api_key_hint.grid(row=0, column=1, sticky="e", padx=(8, 0))

        def refresh_api_key_hint(*_args) -> None:
            if api_key_var.get():
                api_key_hint.grid_remove()
            else:
                api_key_hint.grid()

        api_key_var.trace_add("write", refresh_api_key_hint)
        add_row(3, "API Key", api_key_box)
        refresh_api_key_hint()

        add_row(
            4, "思考模式",
            ttk.Checkbutton(
                card, text="远端模型非思考（默认开，省钱）",
                variable=no_think_var,
            ),
        )
        add_row(5, "模型名称", ttk.Entry(card, textvariable=model_var))
        add_row(6, "识别模式", ttk.Combobox(card, textvariable=mode_var, state="readonly",
                                            values=list(MODE_LABELS.values())))
        add_row(7, "回答类型", ttk.Combobox(card, textvariable=type_var, state="readonly",
                                            values=list(ANSWER_TYPE_LABELS.values())))

        tk.Label(card, text="题库", bg=CARD, fg=MUTED,
                 font=(self.font_family, 9)).grid(
            row=8, column=0, sticky="w", padx=(16, 10), pady=(12, 0))
        bank_buttons = tk.Frame(card, bg=CARD)
        bank_buttons.grid(row=8, column=1, columnspan=2, sticky="w", pady=(12, 0))
        ttk.Button(bank_buttons, text="查看", width=6,
                   command=self.open_bank_file).pack(side="left")
        ttk.Button(bank_buttons, text="清空", width=6,
                   command=lambda: self.clear_bank(dialog)).pack(side="left", padx=(6, 0))
        ttk.Button(bank_buttons, text="从HTML导入", width=11,
                   command=lambda: self.import_html_bank(dialog)).pack(
            side="left", padx=(6, 0))

        note = (
            "如果当前模型是纯文本模型，程序会先用 Windows 自带 OCR 提取截图文字，"
            "再交给模型回答；如果使用视觉模型，自动检测会优先走数学 OCR，"
            "先把公式转写成文本，再交给模型答题。"
            "切换回答类型会自动换成该类型的默认提问，手动改过的提问不会被覆盖。"
            "分析完成后截图会移入 temp 缓存，重新分析从缓存读取。"
        )
        tk.Label(card, text=note, bg=CARD, fg=MUTED, font=(self.font_family, 8),
                 wraplength=480, justify="left").grid(
            row=9, column=0, columnspan=3, sticky="w", padx=16, pady=(16, 0))

        def clear_cache() -> None:
            if self.busy:
                messagebox.showinfo(APP_NAME, "模型正在回答，完成后再清理缓存。", parent=dialog)
                return
            files = self._cache_files()
            if not files:
                messagebox.showinfo("清理缓存", "缓存已经是空的。", parent=dialog)
                return
            total = 0
            for path in files:
                try:
                    total += path.stat().st_size
                except OSError:
                    pass
            if not messagebox.askyesno(
                "清理缓存",
                f"将删除 {len(files)} 个缓存截图（{human_size(total)}）。\n"
                "删除后无法再重新分析这些截图，确定继续吗？",
                parent=dialog,
            ):
                return
            removed, freed, errors = self._clear_cache_files()
            self._after_cache_cleared()
            if errors:
                messagebox.showwarning(
                    "清理缓存",
                    f"已删除 {removed} 项，释放 {human_size(freed)}；"
                    f"{errors} 项可能被占用，未能删除。",
                    parent=dialog,
                )
            else:
                messagebox.showinfo(
                    "清理缓存",
                    f"已删除 {removed} 项，释放 {human_size(freed)}。",
                    parent=dialog,
                )

        footer = tk.Frame(card, bg=CARD)
        footer.grid(row=10, column=0, columnspan=3, sticky="ew", padx=16, pady=(12, 14))
        ttk.Button(footer, text="清理缓存", width=9, command=clear_cache).pack(side="left")
        save_button = ttk.Button(footer, text="保存", width=7, style="Accent.TButton")
        save_button.pack(side="right")
        ttk.Button(footer, text="取消", width=7, command=dialog.destroy).pack(
            side="right", padx=(0, 8))

        def save() -> None:
            folder = Path(folder_var.get().strip().strip('"')).expanduser()
            if not folder.is_dir():
                messagebox.showerror(APP_NAME, "监听目录不存在，请重新选择。", parent=dialog)
                return
            base = base_var.get().strip()
            if not re.match(r"^https?://", base):
                messagebox.showerror(APP_NAME, "接口地址需要以 http:// 或 https:// 开头。", parent=dialog)
                return
            model = model_var.get().strip()
            if not model:
                messagebox.showerror(APP_NAME, "模型名称不能为空。", parent=dialog)
                return
            api_key = api_key_var.get().strip()
            no_think = bool(no_think_var.get())

            self.folder = folder
            self.base_url = base.rstrip("/")
            self.api_key = api_key
            self.deepseek_no_think = no_think
            self.model = model
            self.mode = MODE_BY_LABEL.get(mode_var.get(), "auto")
            new_type = ANSWER_TYPE_BY_LABEL.get(type_var.get(), DEFAULT_ANSWER_TYPE)
            self.answer_type = new_type
            current_prompt = self.prompt_var.get().strip()
            if not current_prompt or current_prompt in ALL_DEFAULT_PROMPTS:
                prompt = prompt_for_type(new_type)
                self.prompt_var.set(prompt)
            else:
                prompt = current_prompt
            self.vision_supported = None
            self.cfg.update({
                "folder": str(folder),
                "base_url": self.base_url,
                "api_key": api_key,
                "deepseek_no_think": no_think,
                "model": model,
                "mode": self.mode,
                "answer_type": new_type,
                "prompt": prompt,
            })
            save_config(self.cfg)
            self.folder_label.configure(text=shorten(str(folder), 36), fg=MUTED)
            self._refresh_mode_text()
            self._reset_baseline(show_newest=True)
            self._detect_async()
            self._set_stage("● 设置已保存", OK)
            dialog.destroy()

        save_button.configure(command=save)
        dialog.bind("<Escape>", lambda _event: dialog.destroy())

    # -- 关闭 ---------------------------------------------------------------

    def open_bank_file(self) -> None:
        if not self.bank_path.exists():
            try:
                self.bank_path.write_text("题号,题目,答案,答案内容\n", encoding="utf-8-sig")
            except OSError as exc:
                messagebox.showerror(APP_NAME, f"无法创建题库文件：{exc}", parent=self)
                return
        try:
            os.startfile(str(self.bank_path))
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"无法打开题库文件：{exc}", parent=self)

    def clear_bank(self, parent=None) -> None:
        parent = parent or self
        if self.busy:
            messagebox.showinfo(APP_NAME, "模型正在回答，完成后再清空题库。", parent=parent)
            return
        entries = load_question_bank(self.bank_path)
        if not entries:
            messagebox.showinfo("清空题库", "题库已经是空的。", parent=parent)
            return
        if not messagebox.askyesno(
            "清空题库",
            f"将清空题库中的 {len(entries)} 道题。\n"
            "清空后需要重新导入才能命中题库，确定继续吗？",
            parent=parent,
        ):
            return
        if not write_question_bank(self.bank_path, []):
            messagebox.showerror(APP_NAME, "清空题库失败。", parent=parent)
            return
        self._bank_cache = None
        messagebox.showinfo("清空题库", "题库已清空。", parent=parent)
        self._set_stage("● 题库已清空", MUTED)

    def import_html_bank(self, parent=None) -> None:
        if self.busy:
            messagebox.showinfo(APP_NAME, "模型正在回答，完成后再导入题库。", parent=parent or self)
            return
        parent = parent or self
        selected = filedialog.askopenfilename(
            parent=parent,
            title="选择题库 HTML",
            initialdir=str(Path.home() / "Downloads"),
            filetypes=[("HTML 文件", "*.html *.htm"), ("所有文件", "*.*")],
        )
        if not selected:
            return
        stats: dict = {}
        imported = parse_html_question_bank(Path(selected), stats)
        if not imported:
            messagebox.showerror(
                APP_NAME,
                "没有从 HTML 中解析到题目。\n请确认它是题库后台保存的表格页面。",
                parent=parent,
            )
            return
        existing = load_question_bank(self.bank_path)
        detail = f"解析到 {len(imported)} 道不重复题目"
        if stats.get("rows"):
            detail += f"（原始 {stats['rows']} 行"
            if stats.get("duplicates"):
                detail += f"，跳过重复 {stats['duplicates']} 行"
            if stats.get("invalid"):
                detail += f"，跳过无效 {stats['invalid']} 行"
            detail += "）"
        if not messagebox.askyesno(
            "导入题库",
            f"{detail}，将合并到当前题库"
            f"（现有 {len(existing)} 题）。\n继续吗？",
            parent=parent,
        ):
            return
        entries, added, updated, removed = merge_question_bank(existing, imported)
        if not write_question_bank(self.bank_path, entries):
            messagebox.showerror(APP_NAME, "写入题库文件失败。", parent=parent)
            return
        self._bank_cache = None
        report = f"导入完成：新增 {added} 题，更新 {updated} 题"
        if removed:
            report += f"，清理重复/无效 {removed} 条"
        report += f"，当前共 {len(entries)} 题。"
        messagebox.showinfo("导入题库", report, parent=parent)
        self._set_stage("● 题库已导入", OK)

    def _on_close(self) -> None:
        self._closing = True
        self._cancel.set()
        self._abort_connection()
        self._stop_screenshot_hook()
        if self._answer_server is not None:
            try:
                self._answer_server.shutdown()
                self._answer_server.server_close()
            except Exception:
                pass
            self._answer_server = None
        try:
            self.cfg["prompt"] = self.prompt_var.get().strip() or prompt_for_type(self.answer_type)
            self.cfg["answer_type"] = self.answer_type
            self.cfg["api_key"] = self.api_key
            self.cfg["deepseek_no_think"] = self.deepseek_no_think
            self.cfg["topmost"] = self.topmost
            save_config(self.cfg)
        except Exception:
            pass
        self.destroy()


# ---------------------------------------------------------------------------

def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="监听截图目录并用本地 Ollama 模型作答")
    parser.add_argument("--folder", help="临时指定监听的截图目录")
    parser.add_argument("--base", help=f"临时指定接口地址（默认 {DEFAULT_BASE}）")
    parser.add_argument("--model", help=f"临时指定模型名称（默认 {DEFAULT_MODEL}）")
    return parser.parse_args(argv)


def main(argv=None) -> int:
    if sys.platform != "win32":
        print("这个程序依赖 Windows 自带的 OCR 和截图目录，请在 Windows 上运行。", file=sys.stderr)
        return 1
    args = parse_args(argv)
    enable_dpi_awareness()
    app = ScreenshotQA(args)
    app.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
