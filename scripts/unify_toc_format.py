#!/usr/bin/env python3
"""
统一Markdown文件的目录格式
标准格式：
- 标题：## 📋 目录
- 空行
- 目录列表使用2空格缩进
- 链接格式：- [标题](#链接)
"""

import os
import re
from pathlib import Path
from typing import List, Tuple, Optional

# 标准目录标题
STANDARD_TOC_HEADER = "## 📋 目录"

def extract_toc_section(content: str) -> Tuple[Optional[str], Optional[int], Optional[int]]:
    """提取目录部分的内容和位置"""
    lines = content.split('\n')

    # 查找目录标题
    toc_start = None
    for i, line in enumerate(lines):
        if re.match(r'^##+\s*📋\s*目录', line) or re.match(r'^##+\s*目录', line):
            toc_start = i
            break

    if toc_start is None:
        return None, None, None

    # 查找目录结束位置（下一个同级别或更高级别的标题）
    toc_end = None
    for i in range(toc_start + 1, len(lines)):
        line = lines[i].strip()
        if not line:
            continue
        if line.startswith('#'):
            # 检查是否是同级别或更高级别的标题
            level = len(line) - len(line.lstrip('#'))
            if level <= 2:  # ## 或更高级别
                toc_end = i
                break

    if toc_end is None:
        toc_end = len(lines)

    toc_content = '\n'.join(lines[toc_start:toc_end])
    return toc_content, toc_start, toc_end

def normalize_toc_indent(content: str) -> str:
    """标准化目录缩进为2空格"""
    lines = content.split('\n')
    normalized = []

    for line in lines:
        if line.strip().startswith('-'):
            # 计算原始缩进
            indent = len(line) - len(line.lstrip())
            # 标准化为2空格倍数
            level = indent // 2
            normalized_line = '  ' * level + line.lstrip()
            normalized.append(normalized_line)
        else:
            normalized.append(line)

    return '\n'.join(normalized)

def fix_toc_format(content: str) -> Tuple[str, bool]:
    """修复目录格式"""
    toc_content, toc_start, toc_end = extract_toc_section(content)

    if toc_content is None:
        return content, False

    lines = content.split('\n')

    # 替换目录部分
    # 确保标题格式正确
    if not lines[toc_start].startswith('## 📋 目录'):
        lines[toc_start] = STANDARD_TOC_HEADER

    # 确保标题后面有空行
    if toc_start + 1 < len(lines) and lines[toc_start + 1].strip():
        lines.insert(toc_start + 1, '')

    # 标准化目录内容缩进
    toc_lines = []
    for i in range(toc_start + 2, toc_end):
        line = lines[i]
        if line.strip().startswith('-'):
            # 标准化缩进
            indent = len(line) - len(line.lstrip())
            level = indent // 2
            normalized_line = '  ' * level + line.lstrip()
            toc_lines.append(normalized_line)
        else:
            toc_lines.append(line)

    # 重建内容
    new_lines = lines[:toc_start + 2] + toc_lines + lines[toc_end:]
    return '\n'.join(new_lines), True

def process_file(file_path: Path) -> bool:
    """处理单个文件"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        new_content, modified = fix_toc_format(content)

        if modified:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(new_content)
            return True
        return False
    except Exception as e:
        print(f"处理文件 {file_path} 时出错: {e}")
        return False

def main():
    """主函数"""
    project_root = Path(__file__).parent.parent
    analysis_dir = project_root / 'analysis'

    if not analysis_dir.exists():
        print(f"目录不存在: {analysis_dir}")
        return

    md_files = list(analysis_dir.rglob('*.md'))
    print(f"找到 {len(md_files)} 个Markdown文件")

    modified_count = 0
    for md_file in md_files:
        if process_file(md_file):
            modified_count += 1
            print(f"已更新: {md_file.relative_to(project_root)}")

    print(f"\n完成！共更新了 {modified_count} 个文件")

if __name__ == '__main__':
    main()
