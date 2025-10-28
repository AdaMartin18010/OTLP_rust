# 项目实用脚本

本目录包含用于项目改进和维护的实用脚本。

## 📋 脚本列表

### 1. 🏥 项目健康度检查 (`check_project_health.sh`)

**用途**: 快速检查项目的整体健康状况

**使用方法**:
```bash
./scripts/check_project_health.sh
```

**检查项目**:
- ✅ Rust工具链版本
- ✅ 项目结构完整性
- ✅ 测试文件覆盖
- ✅ 文档完整性
- ✅ CI/CD配置
- ✅ 安全审计状态
- ✅ 依赖版本冲突

**输出示例**:
```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
🏥 OTLP_rust 项目健康度检查
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

✅ PASS - Rust版本: 1.90.0
✅ PASS - Cargo版本: 1.90.0
✅ PASS - Cargo.toml存在
✅ PASS - crates目录存在 (4个crate)
...

📈 健康度总结
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
通过: 15 | 警告: 3 | 失败: 0

✨ 健康度: 优秀 (83%)
```

---

### 2. 🔧 OpenTelemetry版本冲突修复 (`fix_opentelemetry_conflict.sh`)

**用途**: 自动检测并修复OpenTelemetry版本冲突

**使用方法**:
```bash
./scripts/fix_opentelemetry_conflict.sh
```

**执行步骤**:
1. 检测当前OpenTelemetry版本
2. 识别版本冲突
3. 备份Cargo.toml
4. 添加版本patch统一版本
5. 更新依赖
6. 验证编译

**安全特性**:
- ✅ 自动备份Cargo.toml
- ✅ 用户确认才执行
- ✅ 编译验证
- ✅ 失败自动回滚提示

**输出示例**:
```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
🔧 OpenTelemetry 版本冲突修复工具
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

⚠️  检测到版本冲突: 存在 2 个不同版本
  - 0.30.0
  - 0.31.0

🎯 目标统一版本: 0.31.0

是否要将所有OpenTelemetry依赖统一到 v0.31.0? (y/N)
```

---

### 3. 📊 测试覆盖率设置 (`setup_coverage.sh`)

**用途**: 安装工具并生成测试覆盖率报告

**使用方法**:
```bash
./scripts/setup_coverage.sh
```

**执行步骤**:
1. 检查并安装cargo-tarpaulin
2. 创建覆盖率输出目录
3. 运行测试覆盖率分析
4. 生成多种格式报告(HTML/Lcov/JSON)
5. 创建基准文档

**生成文件**:
```
coverage/
├── index.html                  # HTML报告 (可浏览器打开)
├── cobertura.xml              # Lcov格式
├── tarpaulin-report.json      # JSON数据
├── tarpaulin.log              # 详细日志
└── COVERAGE_BASELINE_YYYY_MM_DD.md  # 基准报告
```

**输出示例**:
```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
📊 测试覆盖率设置和报告生成
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

✅ cargo-tarpaulin 已安装
✅ 创建目录: coverage/
✅ 覆盖率分析完成 (耗时: 120秒)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
📊 覆盖率结果
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

✅ 总体覆盖率: 75% (良好)
```

---

## 🚀 快速开始

### 首次使用推荐流程

```bash
# 1. 检查项目健康度
./scripts/check_project_health.sh

# 2. 如果检测到OpenTelemetry版本冲突，修复它
./scripts/fix_opentelemetry_conflict.sh

# 3. 生成测试覆盖率报告
./scripts/setup_coverage.sh

# 4. 查看覆盖率报告
open coverage/index.html  # macOS
# 或
xdg-open coverage/index.html  # Linux
# 或
start coverage/index.html  # Windows
```

---

## 📝 使用建议

### 定期维护

**每周**:
```bash
# 检查项目健康度
./scripts/check_project_health.sh
```

**每月**:
```bash
# 更新覆盖率报告
./scripts/setup_coverage.sh

# 查看进度
cat coverage/COVERAGE_BASELINE_*.md
```

**发现问题时**:
```bash
# 修复版本冲突
./scripts/fix_opentelemetry_conflict.sh
```

---

## 🔍 故障排查

### 脚本权限问题

```bash
# 如果脚本无法执行，添加执行权限
chmod +x scripts/*.sh
```

### Rust版本问题

```bash
# 更新到Rust 1.90.0
rustup update
rustup default 1.90
```

### 工具安装失败

```bash
# 手动安装工具
cargo install cargo-tarpaulin
cargo install cargo-audit
cargo install cargo-nextest
```

---

## 📚 相关文档

- [执行摘要](../analysis/EXECUTIVE_SUMMARY_2025_10_29.md)
- [完整评估报告](../analysis/CRITICAL_EVALUATION_REPORT_2025_10_29.md)
- [改进行动计划](../analysis/IMPROVEMENT_ACTION_PLAN_2025_10_29.md)

---

## 💡 贡献

如果您有改进脚本的建议，请:
1. Fork项目
2. 创建特性分支
3. 提交Pull Request

---

## 📞 支持

遇到问题？
- 查看脚本输出的错误信息
- 参考改进行动计划文档
- 提交Issue到GitHub

---

*脚本由改进行动计划自动生成，版本: 2025-10-29*

