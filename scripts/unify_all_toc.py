#!/usr/bin/env python3
"""
统一所有Markdown文件的目录格式
1. 确保每个文件只有一个目录
2. 统一目录格式为：## 📋 目录 + 空行 + 目录列表
3. 如果文件没有目录，可以选择添加（暂时跳过）
"""

import os
import re
import sys
from pathlib import Path
from typing import List, Tuple, Optional

STANDARD_TOC_HEADER = "## 📋 目录"

# 排除的目录和文件
EXCLUDE_PATTERNS = [
    '/target/',
    '/.git/',
    '/node_modules/',
    '/.vscode/',
    '/.github/',
]

def should_exclude_file(file_path: str) -> bool:
    """检查文件是否应该被排除"""
    for pattern in EXCLUDE_PATTERNS:
        if pattern in file_path:
            return True
    return False

def find_toc_positions(lines: List[str]) -> List[int]:
    """查找所有目录标题的位置"""
    positions = []
    for i, line in enumerate(lines):
        if re.match(r'^##\s+📋\s+目录\s*$', line) or re.match(r'^##\s+目录\s*$', line):
            positions.append(i)
    return positions

def find_toc_end(lines: List[str], toc_start: int) -> int:
    """查找目录部分的结束位置"""
    for i in range(toc_start + 1, len(lines)):
        line = lines[i].strip()
        if not line:
            continue
        # 找到下一个同级别或更高级别的标题
        if line.startswith('##'):
            return i
    return len(lines)

def remove_duplicate_tocs(lines: List[str]) -> Tuple[List[str], bool]:
    """删除重复的目录，只保留第一个"""
    toc_positions = find_toc_positions(lines)

    if len(toc_positions) <= 1:
        return lines, False

    modified = True
    new_lines = []
    skip_ranges = []

    # 标记需要跳过的范围
    for i in range(1, len(toc_positions)):
        start = toc_positions[i]
        end = find_toc_end(lines, start)
        skip_ranges.append((start, end))

    # 重建内容
    for i, line in enumerate(lines):
        should_skip = False
        for start, end in skip_ranges:
            if start <= i < end:
                should_skip = True
                break
        if not should_skip:
            new_lines.append(line)

    return new_lines, modified

def fix_toc_format(lines: List[str]) -> Tuple[List[str], bool]:
    """统一目录格式"""
    toc_positions = find_toc_positions(lines)

    if not toc_positions:
        return lines, False

    modified = False
    first_toc = toc_positions[0]

    # 检查并修复格式
    new_lines = lines.copy()

    # 修复标题格式
    if not re.match(r'^##\s+📋\s+目录\s*$', new_lines[first_toc]):
        new_lines[first_toc] = STANDARD_TOC_HEADER
        modified = True

    # 确保标题后有空行
    if first_toc + 1 < len(new_lines):
        if new_lines[first_toc + 1].strip():
            new_lines.insert(first_toc + 1, "")
            modified = True
    else:
        new_lines.append("")
        modified = True

    return new_lines, modified

def normalize_indent(lines: List[str]) -> Tuple[List[str], bool]:
    """标准化目录内容的缩进（使用2空格）"""
    toc_positions = find_toc_positions(lines)

    if not toc_positions:
        return lines, False

    modified = False
    new_lines = lines.copy()
    first_toc = toc_positions[0]
    toc_end = find_toc_end(new_lines, first_toc)

    # 标准化目录部分的缩进
    for i in range(first_toc + 2, toc_end):
        line = new_lines[i]
        if line.strip().startswith('-'):
            # 计算当前缩进级别
            indent = len(line) - len(line.lstrip())
            # 标准化为2空格倍数
            level = indent // 2
            normalized_line = '  ' * level + line.lstrip()
            if normalized_line != line:
                new_lines[i] = normalized_line
                modified = True

    return new_lines, False  # 缩进修改不影响整体修改状态

def process_file(file_path: Path) -> dict:
    """处理单个文件"""
    result = {
        'file': str(file_path.relative_to(Path.cwd())),
        'modified': False,
        'has_toc': False,
        'duplicate_removed': False,
        'format_fixed': False,
    }

    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        lines = content.split('\n')
        toc_positions = find_toc_positions(lines)

        if not toc_positions:
            return result

        result['has_toc'] = True

        # 删除重复目录
        if len(toc_positions) > 1:
            lines, removed = remove_duplicate_tocs(lines)
            if removed:
                result['duplicate_removed'] = True
                result['modified'] = True

        # 修复格式
        lines, format_fixed = fix_toc_format(lines)
        if format_fixed:
            result['format_fixed'] = True
            result['modified'] = True

        # 标准化缩进
        lines, _ = normalize_indent(lines)

        # 写回文件
        if result['modified']:
            new_content = '\n'.join(lines)
            # 确保文件以换行符结尾
            if not new_content.endswith('\n'):
                new_content += '\n'

            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(new_content)

    except Exception as e:
        result['error'] = str(e)

    return result

def main():
    """主函数"""
    project_root = Path(__file__).parent.parent

    # 查找所有Markdown文件
    md_files = []
    for path in project_root.rglob('*.md'):
        if not should_exclude_file(str(path)):
            md_files.append(path)

    print("=" * 60)
    print("统一所有Markdown文件的目录格式")
    print("=" * 60)
    print(f"\n找到 {len(md_files)} 个Markdown文件\n")

    # 统计
    stats = {
        'total': len(md_files),
        'processed': 0,
        'no_toc': 0,
        'duplicate_removed': 0,
        'format_fixed': 0,
        'errors': 0,
    }

    # 处理文件
    for md_file in sorted(md_files):
        result = process_file(md_file)

        if result.get('error'):
            print(f"❌ 错误: {result['file']} - {result['error']}")
            stats['errors'] += 1
        elif result['has_toc']:
            stats['processed'] += 1
            if result['duplicate_removed']:
                print(f"🔧 删除重复目录: {result['file']}")
                stats['duplicate_removed'] += 1
            if result['format_fixed']:
                print(f"🔧 统一格式: {result['file']}")
                stats['format_fixed'] += 1
        else:
            stats['no_toc'] += 1

    # 输出统计
    print("\n" + "=" * 60)
    print("处理完成！")
    print("=" * 60)
    print(f"总文件数: {stats['total']}")
    print(f"已有目录: {stats['processed']}")
    print(f"无目录文件: {stats['no_toc']}")
    print(f"删除重复目录: {stats['duplicate_removed']}")
    print(f"统一格式: {stats['format_fixed']}")
    if stats['errors'] > 0:
        print(f"错误: {stats['errors']}")
    print()

if __name__ == '__main__':
    main()
