#!/bin/bash
# 统一所有Markdown文件的目录格式
# 1. 确保每个文件只有一个目录
# 2. 统一目录格式为：## 📋 目录 + 空行 + 目录列表
# 3. 如果文件没有目录，添加一个

set -e

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STANDARD_TOC_HEADER="## 📋 目录"

echo "========================================="
echo "统一所有Markdown文件的目录格式"
echo "========================================="
echo ""

# 统计变量
total_files=0
processed_files=0
no_toc_files=0
duplicate_toc_files=0
fixed_format_files=0

# 处理单个文件
process_file() {
    local file="$1"
    local relative_path="${file#$PROJECT_ROOT/}"
    ((total_files++))

    local modified=false

    # 读取文件内容
    local content=$(cat "$file")
    local lines=()
    while IFS= read -r line; do
        lines+=("$line")
    done <<< "$content"

    # 查找所有目录标题的位置
    local toc_positions=()
    local i=0
    for line in "${lines[@]}"; do
        if [[ "$line" =~ ^##[[:space:]]*📋[[:space:]]*目录[[:space:]]*$ ]] || [[ "$line" =~ ^##[[:space:]]*目录[[:space:]]*$ ]]; then
            toc_positions+=($i)
        fi
        ((i++))
    done

    # 处理多个目录的情况
    if [ ${#toc_positions[@]} -gt 1 ]; then
        echo "🔧 修复重复目录: $relative_path (发现 ${#toc_positions[@]} 个目录)"
        ((duplicate_toc_files++))

        # 只保留第一个目录，删除其他的
        local new_lines=()
        local skip_sections=()

        # 标记需要跳过的行号范围
        for idx in "${!toc_positions[@]}"; do
            if [ $idx -gt 0 ]; then
                local start_line=${toc_positions[$idx]}
                local end_line=${#lines[@]}

                # 找到这个目录部分的结束位置（下一个 ## 标题或文件结尾）
                for ((j=start_line+1; j<${#lines[@]}; j++)); do
                    if [[ "${lines[$j]}" =~ ^##[[:space:]] ]] || [[ "${lines[$j]}" =~ ^#[[:space:]] ]]; then
                        end_line=$j
                        break
                    fi
                done

                skip_sections+=("$start_line:$end_line")
            fi
        done

        # 重建内容，跳过重复的目录部分
        for idx in "${!lines[@]}"; do
            local skip=false
            for section in "${skip_sections[@]}"; do
                local start=${section%%:*}
                local end=${section##*:}
                if [ $idx -ge $start ] && [ $idx -lt $end ]; then
                    skip=true
                    break
                fi
            done
            if [ "$skip" = false ]; then
                new_lines+=("${lines[$idx]}")
            fi
        done

        # 更新内容
        printf '%s\n' "${new_lines[@]}" > "$file"
        content=$(cat "$file")
        lines=()
        while IFS= read -r line; do
            lines+=("$line")
        done <<< "$content"
        modified=true
    fi

    # 统一目录格式
    if [ ${#toc_positions[@]} -gt 0 ]; then
        local first_toc=${toc_positions[0]}

        # 检查格式是否正确
        local needs_fix=false

        # 检查标题格式
        if ! [[ "${lines[$first_toc]}" =~ ^##[[:space:]]*📋[[:space:]]*目录[[:space:]]*$ ]]; then
            needs_fix=true
        fi

        # 检查标题后面是否有空行
        if [ $((first_toc + 1)) -lt ${#lines[@]} ] && [ -n "${lines[$((first_toc + 1))]}" ]; then
            needs_fix=true
        fi

        if [ "$needs_fix" = true ]; then
            echo "🔧 统一格式: $relative_path"
            ((fixed_format_files++))

            # 修复格式
            local new_lines=()
            for idx in "${!lines[@]}"; do
                if [ $idx -eq $first_toc ]; then
                    new_lines+=("$STANDARD_TOC_HEADER")
                    new_lines+=("")
                elif [ $idx -gt $first_toc ] && [ $idx -le $((first_toc + 1)) ]; then
                    if [ $idx -eq $((first_toc + 1)) ] && [ -z "${lines[$idx]}" ]; then
                        # 已经是空行，跳过
                        continue
                    fi
                    if [ $idx -eq $first_toc ]; then
                        continue
                    fi
                    new_lines+=("${lines[$idx]}")
                else
                    new_lines+=("${lines[$idx]}")
                fi
            done

            printf '%s\n' "${new_lines[@]}" > "$file"
            modified=true
        fi

        ((processed_files++))
    else
        # 没有目录，但这是正常的（README.md等可能不需要目录）
        # 暂时跳过自动添加目录，因为需要解析标题结构
        echo "ℹ️  没有目录: $relative_path (跳过自动添加)"
        ((no_toc_files++))
    fi

    if [ "$modified" = true ]; then
        return 0
    fi
    return 1
}

# 主处理循环
echo "开始处理文件..."
echo ""

# 排除某些目录和文件
find "$PROJECT_ROOT" -name "*.md" -type f \
    ! -path "*/target/*" \
    ! -path "*/.git/*" \
    ! -path "*/node_modules/*" \
    | while read -r file; do
    process_file "$file" || true
done

echo ""
echo "========================================="
echo "处理完成！"
echo "========================================="
echo "总文件数: $total_files"
echo "已有目录: $processed_files"
echo "无目录文件: $no_toc_files"
echo "重复目录已修复: $duplicate_toc_files"
echo "格式已统一: $fixed_format_files"
echo ""
