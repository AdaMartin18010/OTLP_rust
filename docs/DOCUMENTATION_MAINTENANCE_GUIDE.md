# 📖 文档维护指南

本指南帮助文档维护者和贡献者高效地维护项目文档。

**最后更新**: 2025年10月24日  
**维护者**: 项目文档团队

---

## 📋 目录

- [文档结构](#文档结构)
- [日常维护任务](#日常维护任务)
- [文件组织规范](#文件组织规范)
- [质量检查清单](#质量检查清单)
- [工具和自动化](#工具和自动化)
- [发布流程](#发布流程)

---

## 📁 文档结构

### 核心导航文件（根目录保留）

```
docs/
├── README.md                          # 文档主页
├── SUMMARY.md                         # mdBook目录
├── INDEX.md                          # 完整索引
├── EXAMPLES_INDEX.md                 # 示例索引
├── DOCUMENTATION_GUIDE.md            # 文档导航指南
├── VISUALIZATION_INDEX.md            # 可视化索引
├── KNOWLEDGE_GRAPH_AND_ANALYSIS.md   # 知识图谱
├── THEORETICAL_FRAMEWORK_INDEX.md    # 理论框架索引
└── book.toml                         # mdBook配置
```

**原则**: 根目录只保留8-10个核心导航文件

---

### 子目录组织

```
docs/
├── api/                    # API参考文档
│   ├── README.md          # API文档索引
│   ├── otlp.md
│   └── reliability.md
│
├── architecture/           # 架构设计文档
│   ├── README.md          # 架构文档索引
│   ├── system-architecture.md
│   └── module-design.md
│
├── examples/              # 示例和教程
│   ├── README.md         # 示例索引
│   ├── basic-examples.md
│   └── advanced-examples.md
│
├── guides/                # 用户指南
│   ├── README.md         # 指南索引
│   ├── quick-start.md
│   ├── installation.md
│   └── ... (其他指南)
│
├── 02_THEORETICAL_FRAMEWORK/  # 理论框架
│   ├── README.md
│   └── ... (理论文档)
│
├── development/           # 开发和维护文档
│   ├── README.md
│   └── ... (开发工具和指南)
│
└── reports/               # 项目报告归档
    ├── README.md
    ├── 2025-01/
    ├── 2025-09/
    ├── 2025-10/
    └── archived/
```

---

## 🔄 日常维护任务

### 每日任务

- [ ] 检查新提交的文档更改
- [ ] 回复文档相关的 Issues
- [ ] 审查待合并的文档 PR
- [ ] 更新 TODO 列表

### 每周任务

- [ ] 运行链接检查工具
- [ ] 检查文档格式一致性
- [ ] 更新文档统计信息
- [ ] 审查用户反馈
- [ ] 更新示例代码的有效性

### 每月任务

- [ ] 全面审查所有文档
- [ ] 更新过时的截图和图表
- [ ] 归档旧的报告文档
- [ ] 更新文档索引和导航
- [ ] 生成文档质量报告
- [ ] 规划下月改进计划

### 季度任务

- [ ] 重大文档重构评估
- [ ] 用户调研和反馈收集
- [ ] 文档工具升级
- [ ] 完整的文档审计
- [ ] 更新文档策略

---

## 📝 文件组织规范

### 根目录文件管理

**只保留以下类型的文件**:

1. **核心导航文件**: README, SUMMARY, INDEX
2. **主要索引文件**: EXAMPLES_INDEX, VISUALIZATION_INDEX
3. **重要指南**: DOCUMENTATION_GUIDE
4. **配置文件**: book.toml

**需要移出根目录的文件**:

- ❌ 报告文档 → `reports/YYYY-MM/`
- ❌ 理论框架文档 → `02_THEORETICAL_FRAMEWORK/`
- ❌ 开发工具文档 → `development/`
- ❌ 临时工作文档 → 删除或归档

### 文件命名规范

**Markdown 文件**:

```
# 英文文档 (kebab-case)
quick-start.md
system-architecture.md
api-reference.md

# 报告文档 (UPPER_SNAKE_CASE + 日期)
PROJECT_STATUS_2025_10_24.md
DOCUMENTATION_ENHANCEMENT_BATCH1_2025_10_05.md

# 中文文档
项目总结_2025_10_24.md
文档优化报告_2025_10_24.md
```

**目录命名**:

```
# 英文目录 (kebab-case 或 snake_case)
api/
user-guides/
02_THEORETICAL_FRAMEWORK/

# 报告归档 (YYYY-MM)
reports/2025-10/
reports/archived/
```

### 子目录必备文件

每个主要子目录都应该有:

1. **README.md** - 目录索引和导航
2. **必要的文档文件** - 实际内容
3. **assets/** (如需要) - 图片和媒体文件

---

## ✅ 质量检查清单

### 新文档检查

创建或更新文档时，检查以下项目:

#### 内容质量

- [ ] 标题清晰准确
- [ ] 有完整的目录
- [ ] 内容组织合理
- [ ] 代码示例可运行
- [ ] 包含实际使用场景
- [ ] 技术信息准确
- [ ] 语言简洁易懂

#### 格式规范

- [ ] 使用正确的 Markdown 语法
- [ ] 标题层级正确（H1 → H2 → H3）
- [ ] 代码块有语言标注
- [ ] 列表格式统一
- [ ] 链接格式正确
- [ ] 图片有alt文本

#### 链接和引用

- [ ] 所有内部链接有效
- [ ] 外部链接可访问
- [ ] 引用的文件存在
- [ ] 相对路径正确
- [ ] 交叉引用完整

#### 元数据

- [ ] 有创建/更新日期
- [ ] 有版本信息（如适用）
- [ ] 有作者信息（如适用）
- [ ] 有相关资源链接

---

## 🛠️ 工具和自动化

### 推荐工具

#### 1. Markdown 编辑器

- **VS Code** + Markdown All in One 插件
- **Typora** - 所见即所得编辑器
- **Mark Text** - 开源 Markdown 编辑器

#### 2. 链接检查

```bash
# 使用 markdown-link-check
npx markdown-link-check docs/**/*.md

# 使用 mdbook test
cd docs && mdbook test
```

#### 3. 格式化

```bash
# 使用 prettier
npx prettier --write "docs/**/*.md"

# 使用 markdownlint
npx markdownlint docs/**/*.md --fix
```

#### 4. 文档构建

```bash
# 构建 mdBook
cd docs && mdbook build

# 本地预览
cd docs && mdbook serve

# 清理构建
cd docs && mdbook clean
```

### 自动化脚本

创建 `docs/scripts/` 目录，包含:

```bash
# check-links.sh - 链接检查
# format-docs.sh - 文档格式化
# build-docs.sh - 文档构建
# update-toc.sh - 更新目录
# generate-index.sh - 生成索引
```

---

## 🚀 发布流程

### 1. 准备阶段

```bash
# 1. 切换到文档分支
git checkout docs/update-YYYY-MM-DD

# 2. 确保最新代码
git pull origin main

# 3. 检查文档质量
bash docs/scripts/check-links.sh
bash docs/scripts/format-docs.sh
```

### 2. 构建阶段

```bash
# 1. 构建文档
cd docs && mdbook build

# 2. 检查构建输出
ls -la book/

# 3. 本地预览
mdbook serve
```

### 3. 审查阶段

- [ ] 自我审查所有更改
- [ ] 运行质量检查清单
- [ ] 验证所有链接
- [ ] 测试代码示例
- [ ] 检查移动端显示

### 4. 提交阶段

```bash
# 1. 添加更改
git add docs/

# 2. 提交更改
git commit -m "docs: [描述] - YYYY-MM-DD

- 详细变更1
- 详细变更2
- 详细变更3
"

# 3. 推送到远程
git push origin docs/update-YYYY-MM-DD
```

### 5. 发布阶段

1. 创建 Pull Request
2. 请求文档审查
3. 处理审查意见
4. 合并到 main 分支
5. 触发文档部署
6. 验证在线文档

---

## 📊 文档归档规范

### 报告归档

**时机**: 每月月底或有大量新报告时

**步骤**:

```bash
# 1. 检查需要归档的报告
cd docs
ls -la *.md | grep "2025_10"

# 2. 移动到对应月份目录
mv REPORT_2025_10_*.md reports/2025-10/

# 3. 更新 reports/README.md

# 4. 提交更改
git add reports/
git commit -m "docs: 归档2025年10月报告"
```

**原则**:

- 当前月份的报告保留在 `reports/YYYY-MM/`
- 超过6个月的报告可移到 `reports/archived/`
- 重要里程碑报告永久保留
- 更新归档目录的 README

---

## 💡 最佳实践

### DO ✅

- **保持简洁**: 文档简洁明了，避免冗余
- **用户导向**: 从用户角度编写文档
- **实例驱动**: 提供具体可运行的示例
- **持续更新**: 代码变更时同步更新文档
- **一致性**: 保持格式和风格的一致性
- **版本控制**: 重要文档保留历史版本
- **反馈驱动**: 根据用户反馈改进文档

### DON'T ❌

- **避免根目录堆积**: 不要在根目录放置过多文件
- **避免重复内容**: 使用链接代替重复
- **避免过时示例**: 及时更新代码示例
- **避免死链接**: 定期检查并修复链接
- **避免假设知识**: 解释关键概念
- **避免技术黑话**: 使用易懂的语言
- **避免忽略反馈**: 重视用户的文档问题

---

## 🔍 故障排查

### 链接失效

```bash
# 查找损坏的链接
npx markdown-link-check docs/**/*.md

# 批量替换链接
find docs -name "*.md" -exec sed -i 's/old-path/new-path/g' {} +
```

### 格式问题

```bash
# 检查 Markdown 语法
npx markdownlint docs/**/*.md

# 自动修复常见问题
npx markdownlint docs/**/*.md --fix
```

### 构建失败

```bash
# 清理并重新构建
cd docs
mdbook clean
mdbook build

# 检查 book.toml 配置
mdbook test
```

---

## 📞 获取帮助

### 内部资源

- [文档开发指南](development/README.md)
- [文档模板](development/DOCUMENT_TEMPLATE.md)
- [自动化工具](development/DOCUMENTATION_AUTOMATION_TOOLS.md)

### 外部资源

- [Markdown 指南](https://www.markdownguide.org/)
- [mdBook 文档](https://rust-lang.github.io/mdBook/)
- [文档写作指南](https://developers.google.com/tech-writing)

### 联系维护者

- **GitHub Issues**: 报告文档问题
- **GitHub Discussions**: 讨论文档改进
- **Email**: docs@your-org.com

---

## 📝 更新日志

### 2025-10-24

- ✅ 创建文档维护指南
- ✅ 定义文件组织规范
- ✅ 建立质量检查清单
- ✅ 制定发布流程

---

**维护者**: 项目文档团队  
**版本**: 1.0.0  
**下次审查**: 2025-11-24

