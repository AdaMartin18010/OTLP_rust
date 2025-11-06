#!/bin/bash
# 删除重复的目录部分，只保留第一个

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

find "$PROJECT_ROOT" -name "*.md" -type f | while read -r file; do
    # 查找所有 "## 📋 目录" 的位置
    toc_lines=$(grep -n "^## 📋 目录$" "$file" 2>/dev/null | cut -d: -f1)

    if [ -z "$toc_lines" ]; then
        continue
    fi

    toc_count=$(echo "$toc_lines" | wc -l)

    if [ "$toc_count" -gt 1 ]; then
        echo "处理文件: $file (发现 $toc_count 个目录)"

        # 获取第一个目录的行号
        first_toc=$(echo "$toc_lines" | head -1)

        # 获取所有目录的行号（除了第一个）
        other_tocs=$(echo "$toc_lines" | tail -n +2)

        # 从后往前删除，避免行号变化
        echo "$other_tocs" | tac | while read -r line_num; do
            if [ -n "$line_num" ]; then
                # 找到这个目录部分的结束位置（下一个 ## 标题）
                end_line=$(sed -n "${line_num},\$p" "$file" | grep -n "^##" | head -2 | tail -1 | cut -d: -f1)

                if [ -z "$end_line" ]; then
                    # 如果没有找到下一个标题，删除到文件末尾
                    end_line=$(wc -l < "$file")
                else
                    end_line=$((line_num + end_line - 2))
                fi

                # 删除目录部分（包括标题和空行）
                # 先删除目录内容，再删除标题
                if [ "$end_line" -gt "$line_num" ]; then
                    # 使用临时文件
                    temp_file=$(mktemp)
                    # 删除从 line_num 到 end_line 的行
                    sed "${line_num},${end_line}d" "$file" > "$temp_file"
                    mv "$temp_file" "$file"
                else
                    # 只删除目录标题行
                    sed "${line_num}d" "$file" > "${file}.tmp"
                    mv "${file}.tmp" "$file"
                fi
            fi
        done

        echo "  ✓ 已删除重复的目录部分"
    fi
done

echo "完成！"
