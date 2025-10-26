# OTLP Rust 架构规划总结

> **规划日期**: 2025-10-20  
> **状态**: 待执行  
> **预计完成**: 12 周

---

## 📋 规划概览

本次架构规划的核心目标是将现有的 `otlp` 和 `reliability` 两个 crate 进行更清晰的组织和整合，形成一个层次分明、职责清晰、易于维护的 crate 生态系统。

---

## 🎯 核心目标

1. **关注点分离**: 将核心功能、传输、应用层等不同职责分离到不同 crate
2. **减少编译时间**: 通过细粒度的 crate 拆分实现增量编译优化
3. **提升可维护性**: 清晰的模块边界和依赖关系
4. **改善用户体验**: 提供从轻量级到完整功能的渐进式选择
5. **统一文档体系**: 重组文档目录，建立清晰的文档导航

---

## 🏗️ 新架构概览

### Crate 层次结构

```text
L0 (基础) - opentelemetry 0.31.0 + Rust std
    ↓
L1 (核心) - otlp-core, otlp-proto, otlp-transport
    ↓
L2 (功能) - otlp, reliability, otlp-microservices
    ↓
L3 (整合) - otlp-reliability-bridge, otlp-integrations
    ↓
L4 (应用) - otlp-cli, otlp-examples, otlp-benchmarks
```

### 新增 Crates

| Crate | 职责 | 状态 |
|-------|------|------|
| `otlp-core` | 核心数据模型和类型 | 待创建 |
| `otlp-proto` | Protobuf 编解码 | 待创建 |
| `otlp-transport` | 网络传输层 | 待创建 |
| `otlp-microservices` | 微服务支持 | 待创建（从 otlp 提取）|
| `otlp-reliability-bridge` | OTLP + Reliability 深度整合 | 待创建 |
| `otlp-integrations` | 外部系统集成 | 待创建 |
| `otlp-cli` | 命令行工具 | 待创建 |

### 重构 Crates

| Crate | 变更 | 状态 |
|-------|------|------|
| `otlp` | 重构为使用新核心 crates，简化模块结构 | 待重构 |
| `reliability` | 增强特性，明确对核心的依赖关系 | 待增强 |

---

## 📚 文档重组

### 新文档结构

```text
docs/
├── architecture/       # 架构设计
├── guides/            # 用户指南
│   ├── getting-started/
│   ├── tutorials/
│   ├── howto/
│   └── best-practices/
├── api/               # API 参考
├── design/            # 设计文档
│   ├── rfcs/
│   ├── decisions/
│   └── specifications/
├── implementation/    # 实现细节
│   ├── semantic-models/
│   ├── algorithms/
│   └── optimizations/
├── operations/        # 运维文档
│   ├── deployment/
│   ├── monitoring/
│   └── maintenance/
├── reports/           # 报告
│   ├── benchmarks/
│   ├── performance/
│   └── progress/
├── research/          # 研究
├── contributing/      # 贡献指南
└── reference/         # 参考资料
```

### 文档工具

- **mdBook**: 生成文档站点
- **rustdoc**: API 文档
- **文档索引**: 统一的文档导航

---

## 🛣️ 实施路线图

### 阶段 1: 核心拆分（第 1-2 周）

- [x] 创建规划文档
- [ ] 创建 `otlp-core` crate
- [ ] 创建 `otlp-proto` crate
- [ ] 创建 `otlp-transport` crate
- [ ] 验证：所有测试通过

### 阶段 2: 主 Crate 重构（第 3-4 周）

- [ ] 重构 `otlp` 使用新核心 crates
- [ ] 增强 `reliability` crate
- [ ] 清理冗余代码
- [ ] 验证：所有示例正常

### 阶段 3: 提取专项 Crates（第 5-6 周）

- [ ] 创建 `otlp-microservices`
- [ ] 创建 `otlp-integrations`
- [ ] 验证：集成测试通过

### 阶段 4: 整合层（第 7-8 周）

- [ ] 创建 `otlp-reliability-bridge`
- [ ] 实现统一可观测性
- [ ] 验证：端到端测试

### 阶段 5: 工具和文档（第 9-10 周）

- [ ] 创建 `otlp-cli`
- [ ] 整理示例和基准测试
- [ ] 文档迁移和重组
- [ ] 生成文档站点

### 阶段 6: 发布准备（第 11-12 周）

- [ ] 性能基准测试
- [ ] 安全审计
- [ ] API 稳定性评审
- [ ] 发布到 crates.io

---

## 📊 预期收益

### 技术收益

- **编译时间**: 预计减少 30-50%（通过增量编译）
- **二进制大小**: 按需选择特性，最小化可减少 70%
- **开发效率**: 模块边界清晰，并行开发更容易
- **测试速度**: 局部测试更快

### 用户收益

- **学习曲线**: 渐进式功能采用，从简单到复杂
- **依赖管理**: 明确的依赖层次，减少冲突
- **文档体验**: 结构化文档，易于导航和搜索
- **功能选择**: 灵活的特性组合

### 维护收益

- **代码质量**: 单一职责，易于理解和修改
- **版本管理**: 独立的版本发布节奏
- **影响范围**: 局部修改影响范围小
- **技术债务**: 清理冗余，降低技术债

---

## 📁 关键文件

1. **[CRATE_ARCHITECTURE_PLAN.md](CRATE_ARCHITECTURE_PLAN.md)**  
   完整的架构规划文档（50+ 页）

2. **[CRATE_QUICK_REFERENCE.md](CRATE_QUICK_REFERENCE.md)**  
   快速参考手册（1 页速查）

3. **[scripts/reorganize-docs.ps1](scripts/reorganize-docs.ps1)**  
   文档重组自动化脚本

4. **[docs/book.toml](docs/book.toml)**  
   mdBook 配置文件

5. **[docs/SUMMARY.md](docs/SUMMARY.md)**  
   文档站点目录结构

---

## 🚀 如何开始

### 1. 查看规划文档

```bash
# 阅读完整规划
cat CRATE_ARCHITECTURE_PLAN.md

# 快速参考
cat CRATE_QUICK_REFERENCE.md
```

### 2. 运行文档重组（可选）

```bash
# 模拟运行，查看会做什么
.\scripts\reorganize-docs.ps1 -DryRun

# 实际执行
.\scripts\reorganize-docs.ps1
```

### 3. 生成文档站点

```bash
# 安装 mdBook
cargo install mdbook

# 构建文档
cd docs
mdbook build

# 本地预览
mdbook serve
```

### 4. 开始实施

按照路线图，从阶段 1 开始：

```bash
# 创建第一个核心 crate
cargo new --lib otlp-core
cd otlp-core

# 设置 Cargo.toml
# 开始迁移代码
```

---

## ⚠️ 注意事项

### 破坏性变更

这次重构会引入一些破坏性变更：

1. **包名变更**: `otlp` 的部分模块会移到新 crate
2. **导入路径**: 需要更新 `use` 语句
3. **特性标志**: 特性名称可能调整

### 迁移建议

- **保持向后兼容**: 在 `otlp` 中重新导出新 crate 的类型
- **提供迁移指南**: 详细的升级文档
- **版本策略**: 主版本号升级（0.1 → 0.2）
- **过渡期**: 保留旧 API 一段时间，标记为 `#[deprecated]`

### 风险缓解

1. **完整的测试**: 确保所有测试在重构后仍然通过
2. **分阶段实施**: 按路线图逐步推进，每个阶段验证
3. **回滚计划**: 保留原始代码分支，必要时可回滚
4. **社区沟通**: 提前通知用户即将到来的变更

---

## 🤝 参与贡献

欢迎参与架构规划的讨论和实施！

### 反馈渠道

- **GitHub Issues**: 提出问题和建议
- **GitHub Discussions**: 参与设计讨论
- **Pull Requests**: 提交代码实现

### 讨论议题

可以讨论的话题：

1. Crate 拆分的粒度是否合适？
2. 依赖关系是否清晰合理？
3. 文档结构是否易于导航？
4. 迁移路线图是否可行？
5. 是否有遗漏的使用场景？

---

## 📈 进度跟踪

### GitHub Project Board

建议创建 GitHub Project 跟踪进度：

- **待办**: 尚未开始的任务
- **进行中**: 正在实施的任务
- **审查中**: 等待 Code Review
- **已完成**: 已合并到主分支

### 里程碑

- **M1**: 核心 Crates 创建完成（第 2 周末）
- **M2**: 主 Crate 重构完成（第 4 周末）
- **M3**: 专项 Crates 创建完成（第 6 周末）
- **M4**: 整合层完成（第 8 周末）
- **M5**: 文档和工具完成（第 10 周末）
- **M6**: 发布准备完成（第 12 周末）

---

## 📚 参考资料

### 内部文档

- [原有项目架构](analysis/INDEX.md)
- [性能基准报告](benchmarks/results/)
- [项目进度报告](docs/reports/2025-10/)

### 外部资源

- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [Cargo Book - Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html)
- [OpenTelemetry Specification](https://opentelemetry.io/docs/specs/otlp/)

---

## 💬 常见问题

### Q1: 为什么要拆分 crate？

**A**: 主要为了：

1. 减少编译时间（增量编译）
2. 明确职责边界（单一职责原则）
3. 灵活的依赖选择（按需引入）
4. 更好的并行开发（团队协作）

### Q2: 会影响现有用户吗？

**A**: 会有影响，但我们会：

1. 保持主要的 API 向后兼容
2. 提供详细的迁移指南
3. 在 `otlp` crate 中重新导出常用类型
4. 标记过时 API 为 `#[deprecated]`

### Q3: 什么时候完成？

**A**: 预计 12 周完成全部重构，但会分阶段发布：

- 第 2 周: 核心 crates 可用
- 第 4 周: 重构后的主 crate 可用
- 第 8 周: 完整功能可用
- 第 12 周: 正式发布

### Q4: 如何参与？

**A**: 欢迎通过以下方式参与：

1. 在 Issues 中提出建议
2. 在 Discussions 中参与讨论
3. 提交 Pull Request
4. 帮助审查代码和文档

---

## 📝 更新日志

- **2025-10-20**: 初始架构规划发布
  - 完成整体架构设计
  - 创建详细规划文档
  - 制定实施路线图
  - 设计新文档结构

---

**维护者**: OTLP Rust Team  
**最后更新**: 2025-10-20  
**文档版本**: 1.0
