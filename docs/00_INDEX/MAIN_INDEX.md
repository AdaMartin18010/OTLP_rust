# 文档索引

**版本**: 2.0  
**最后更新**: 2025年10月26日  
**状态**: 🟢 活跃维护

> **简介**: OTLP Rust 项目主文档索引 - 完整的文档导航、分类和学习路径。

---

## 📋 目录

- [文档索引](#文档索引)
  - [📋 目录](#-目录)
  - [🏗️ Crate 架构文档 (2025-10-26 新增)](#️-crate-架构文档-2025-10-26-新增)
    - [🚀 快速开始](#-快速开始)
    - [📚 架构理论文档](#-架构理论文档)
  - [📚 文档结构](#-文档结构)
  - [🚀 快速开始](#-快速开始-1)
  - [📚 编号目录体系（主要文档结构）](#-编号目录体系主要文档结构)
  - [📖 指南文档 (`guides/`) - 快速参考](#-指南文档-guides---快速参考)
  - [🏛️ 架构和设计](#️-架构和设计)
  - [🔬 理论框架](#-理论框架)
  - [📚 API 和参考](#-api-和参考)
  - [🛠️ 开发和贡献](#️-开发和贡献)
  - [📊 分析和报告](#-分析和报告)
  - [🗺️ 学习路径](#️-学习路径)
    - [初学者路径](#初学者路径)
    - [开发者路径](#开发者路径)
    - [架构师路径](#架构师路径)
    - [研究者路径](#研究者路径)
  - [📚 文档质量](#-文档质量)
  - [🔗 相关资源](#-相关资源)

---

## 🏗️ Crate 架构文档 (2025-10-26 新增)

**项目重组**: 四个crate的架构重新定位和完整知识体系

### 🚀 快速开始

| Crate | 使用指南 ⭐ NEW | 完整文档 |
|-------|----------------|----------|
| **libraries** 📚 | [使用指南](09_CRATES/libraries_guide.md) | [完整文档](../crates/libraries/docs/README.md) |
| **model** 🎨 | [使用指南](09_CRATES/model_guide.md) | [完整文档](../crates/model/docs/README.md) |
| **reliability** ⚡ | [使用指南](09_CRATES/reliability_guide.md) | [完整文档](../crates/reliability/docs/README.md) |
| **otlp** 📊 | [使用指南](09_CRATES/otlp_guide.md) | [完整文档](../crates/otlp/docs/README.md) |

📖 **Crates 总览**: [09_CRATES/README.md](09_CRATES/README.md) ⭐ NEW

### 📚 架构理论文档

| 文档 | 说明 | 规模 |
|------|------|------|
| [架构重组计划](CRATES_ARCHITECTURE_REORG_2025_10_26.md) | 四crate定位、代码组织、实施计划 | 10,000+ 字 |
| [知识图谱](CRATES_KNOWLEDGE_GRAPH_2025_10_26.md) | 概念定义、属性、关系、扩展路径 | 15,000+ 字 |
| [矩阵对比](CRATES_MATRIX_COMPARISON_2025_10_26.md) | 10维度对比、学习路径、决策支持 | 12,000+ 字 |
| [工作总结](CRATES_REORGANIZATION_SUMMARY_2025_10_26.md) | 重组工作完成情况和下一步计划 | 5,000+ 字 |

**总计**: 8个核心文档（含4个使用指南），60,000+ 字，137+ 概念定义，23+ 图表

---

## 📚 文档结构

本项目文档按照功能和时间组织，便于查找和追溯。

---

## 🚀 快速开始

> 📖 **推荐**: 完整入门教程请访问 [01_GETTING_STARTED](01_GETTING_STARTED/README.md) (268 行完整指南)

- [🎯 快速开始指南](01_GETTING_STARTED/README.md) - **完整版**，系统要求、安装、配置、验证
- [快速开始](guides/quick-start.md) - **快速版**，5分钟上手项目
- [安装指南](guides/installation.md) - 环境配置和安装步骤
- [贡献指南](guides/CONTRIBUTING.md) - 如何贡献代码
- [开发工作流](guides/DEVELOPMENT_WORKFLOW.md) - 开发规范和流程

---

## 📚 编号目录体系（主要文档结构）

> 💡 **推荐阅读**: 编号目录（01-08）提供了最完整、最系统化的文档

| 目录 | 说明 | 行数 |
|------|------|------|
| [01_GETTING_STARTED/](01_GETTING_STARTED/README.md) | 🎯 快速开始 - 完整入门教程 | 268+ |
| [02_THEORETICAL_FRAMEWORK/](02_THEORETICAL_FRAMEWORK/README.md) | 🔬 理论框架 - 形式化模型与理论基础 | 17 文件 |
| [03_API_REFERENCE/](03_API_REFERENCE/README.md) | 🔧 API 参考 - 完整 API 文档 | 3000+ |
|   | ┣━ [API快速参考](03_API_REFERENCE/API_QUICK_REFERENCE.md) ⭐ NEW | 速查卡片 |
|   | ┣━ [Profiling API](03_API_REFERENCE/profiling_api.md) ⭐ NEW | 500+ 行 |
|   | ┣━ [SIMD API](03_API_REFERENCE/simd_api.md) ⭐ NEW | 650+ 行 |
|   | ┣━ [Compression API](03_API_REFERENCE/compression_api.md) ⭐ NEW | 600+ 行 |
|   | ┗━ [Semantic Conventions](03_API_REFERENCE/semantic_conventions_api.md) ⭐ NEW | 700+ 行 |
| [04_ARCHITECTURE/](04_ARCHITECTURE/README.md) | 🏛️ 架构设计 - 微服务架构、性能优化 | 653+ |
| [05_IMPLEMENTATION/](05_IMPLEMENTATION/README.md) | 🛠️ 实现指南 - Profile/Event/Arrow 实现 | 2462+ |
| [06_DEPLOYMENT/](06_DEPLOYMENT/README.md) | 🚀 部署运维 - 生产部署、监控、调优 | 1213+ |
| [07_INTEGRATION/](07_INTEGRATION/README.md) | 🔗 集成指南 - OTel、服务网格、云原生 | 1359+ |
| [08_REFERENCE/](08_REFERENCE/README.md) | 📚 参考资料 - OTLP 标准、最佳实践 | 2100+ |

**总计**: 8 大主题，8600+ 行高质量文档

---

## 📖 指南文档 (`guides/`) - 快速参考

> 💡 **适用场景**: 快速查阅和实战操作

| 文档 | 说明 |
|------|------|
| [quick-start.md](guides/quick-start.md) | 快速开始指南 |
| [installation.md](guides/installation.md) | 安装指南 |
| [otlp-client.md](guides/otlp-client.md) | OTLP 客户端使用指南 |
| [reliability-framework.md](guides/reliability-framework.md) | 可靠性框架使用指南 |
| [performance-optimization.md](guides/performance-optimization.md) | 性能优化指南 |
| [monitoring.md](guides/monitoring.md) | 监控配置指南 |
| [deployment.md](guides/deployment.md) | 部署指南 |
| [troubleshooting.md](guides/troubleshooting.md) | 故障排除指南 |
| [CONTRIBUTING.md](guides/CONTRIBUTING.md) | 贡献指南 |
| [DEVELOPMENT_WORKFLOW.md](guides/DEVELOPMENT_WORKFLOW.md) | 开发工作流 |
| [COMMUNITY_GUIDE.md](guides/COMMUNITY_GUIDE.md) | 社区指南 |
| [RELEASE_PREPARATION.md](guides/RELEASE_PREPARATION.md) | 发布准备 |

---

## 📊 报告归档 (`reports/`)

### 2025年10月报告 (`reports/2025-10/`)

最新的项目报告和文档：

- `Cargo配置升级报告_2025_10_20.md` - Cargo配置全面梳理
- `CRITICAL_EVALUATION_REPORT_2025_10_18.md` - 批判性评估
- `FINAL_COMPLETION_REPORT_2025_10_18.md` - 最终完成报告
- `PROJECT_STATUS_DASHBOARD_2025_10_18.md` - 项目状态仪表盘
- 以及更多Phase报告、工作总结等

### 历史报告 (`reports/archived/`)

- `2025-10-04` ~ `2025-10-08` - 早期10月报告
- 依赖升级报告
- 项目清理和组织报告
- 文档一致性报告

### 2025年9月报告 (`reports/2025-09/`)

- 配置文件升级总结
- 系统时间同步配置

### 2025年1月报告 (`reports/2025-01/`)

- 性能优化报告
- 综合修复报告

---

## 🔧 技术文档 (`technical/`)

### 架构文档 (`technical/architecture/`)

- 语义模型框架
- 理论框架文档
- 自我运维架构指南
- 集成框架文档

### Rust 1.90 (`technical/rust-1.90/`)

- 实施计划
- 性能优化最佳实践指南
- 特性梳理与项目完善分析
- 项目完善最终报告

### OTLP 标准 (`technical/otlp-standards/`)

- OTLP标准对齐改进建议
- 标准深度梳理（`标准深度梳理_2025_10/`）

---

## 📅 规划文档 (`planning/`)

### 路线图 (`planning/roadmaps/`)

- 持续改进路线图
- 结构优化实施计划

### 行动计划 (`planning/action-plans/`)

- 下一步行动
- 立即行动清单（历史）

---

## 🔬 基准测试 (`../benchmarks/`)

### 测试结果 (`benchmarks/results/`)

- `2025-10-06_benchmark_results.txt` - 综合基准测试结果
- `2025-10-06_otlp_results.txt` - OTLP专项测试结果
- 性能基准测试报告（2025-10-04, 2025-10-06）

### 测试计划 (`benchmarks/plans/`)

- `2025-10-18_plan.md` - 2025年10月18日测试计划

---

## 🐳 Docker 配置 (`../docker/`)

- `Dockerfile` - 开发环境
- `Dockerfile.production` - 生产环境
- `README.md` - 使用说明

---

## 📜 脚本工具 (`../scripts/`)

### 工具脚本 (`scripts/utils/`)

- `fix_clippy_warnings.sh` - 修复Clippy警告
- `sync_time.ps1` - 系统时间同步

---

## 📚 参考资料 (`08_REFERENCE/`)

| 文档 | 说明 |
|------|------|
| [README.md](08_REFERENCE/README.md) | 参考资料总览 |
| [otlp_standards_alignment.md](08_REFERENCE/otlp_standards_alignment.md) | 🌟 OTLP 标准对齐 (1300+ 行) - NEW! |
| [otlp_2024_2025_features.md](08_REFERENCE/otlp_2024_2025_features.md) | 🚀 OTLP 2024-2025 特性 (800+ 行) - NEW! |
| [rust_1.90_otlp_tech_stack_alignment.md](08_REFERENCE/rust_1.90_otlp_tech_stack_alignment.md) | 🦀 Rust 1.90 技术栈对齐 (3000+ 行) - NEW! |
| [best_practices.md](08_REFERENCE/best_practices.md) | 最佳实践指南 |
| [glossary.md](08_REFERENCE/glossary.md) | 术语表 |
| [standards_compliance.md](08_REFERENCE/standards_compliance.md) | 标准合规性 |
| [troubleshooting_guide.md](08_REFERENCE/troubleshooting_guide.md) | 故障排除指南 |

---

## 🛠️ 实现指南 (`05_IMPLEMENTATION/`)

> 🆕 **OTLP 2024-2025 新特性实现**

| 文档 | 说明 |
|------|------|
| [README.md](05_IMPLEMENTATION/README.md) | 实现指南总览 |
| [profile_signal_implementation_guide.md](05_IMPLEMENTATION/profile_signal_implementation_guide.md) | 🔥 Profile 信号实现指南 (885 行) - NEW! |
| [event_signal_implementation_guide.md](05_IMPLEMENTATION/event_signal_implementation_guide.md) | ⚡ Event 信号实现指南 (1011 行) - NEW! |
| [otlp_arrow_configuration_guide.md](05_IMPLEMENTATION/otlp_arrow_configuration_guide.md) | 🚀 OTLP/Arrow 配置指南 (430 行) - NEW! |

**核心内容**:
- Profile 数据采集与导出 | CPU/内存/锁分析 | 持续性能分析
- Event vs Logs 对比 | 结构化事件处理 | 业务事件跟踪
- Apache Arrow 集成 | 列式内存格式 | 零拷贝优化

---

## 🔍 查找文档建议

### 按时间查找

1. **最新状态** → `reports/2025-10/`
2. **历史追溯** → `reports/archived/`

### 按类型查找

1. **快速上手** → `guides/QUICK_START.md`
2. **技术细节** → `technical/`
3. **项目规划** → `planning/`
4. **性能数据** → `../benchmarks/`

### 按主题查找

- **Rust 1.90** → `technical/rust-1.90/`
- **OTLP标准** → `technical/otlp-standards/`
- **架构设计** → `technical/architecture/`
- **依赖管理** → `reports/archived/` （搜索"依赖"）

---

## 📝 命名规范

- **报告文件**: `YYYY-MM-DD_描述.md`
- **目录名称**: 小写字母 + 连字符（如 `action-plans/`）
- **归档规则**: 按月份归档（`2025-10/`, `2025-09/`）

---

## 🔗 相关资源

- [项目主README](../README.md) - 项目总览
- [CHANGELOG](../CHANGELOG.md) - 变更日志
- [LICENSE](../LICENSE) - 许可证

---

## 💡 维护说明

本索引文档需要在以下情况更新：

1. 添加新的主要文档或报告
2. 调整目录结构
3. 每月归档时

**维护责任**: 项目维护者  
**更新频率**: 每月或重大变更时
