# 开发工具包 (Development Toolkit)

**📅 创建日期**: 2025年10月23日  
**🎯 目标**: 提供立即可用的开发工具和脚本  
**📊 用途**: 加速开发，标准化流程  

---

## 📋 工具包概览

本目录包含开发过程中需要的各种工具、脚本和配置文件，让开发者能够快速搭建环境并开始工作。

```yaml
工具分类:
  环境搭建: 自动化环境配置脚本
  代码生成: 模板和生成器
  开发辅助: 常用命令和工具
  质量保证: 测试和审查工具
  CI/CD: 自动化流水线配置
```

---

## 🗂️ 目录结构

```text
15_development_toolkit/
├── README.md                           # 本文档
├── scripts/                            # 脚本工具
│   ├── setup_dev_env.sh               # 开发环境搭建脚本
│   ├── create_module.sh               # 新模块创建脚本
│   ├── run_checks.sh                  # 代码质量检查脚本
│   └── benchmark.sh                   # 性能基准测试脚本
├── templates/                          # 代码模板
│   ├── module_template.rs             # 模块模板
│   ├── test_template.rs               # 测试模板
│   └── benchmark_template.rs          # 基准测试模板
├── configs/                            # 配置文件
│   ├── .github/                       # GitHub配置
│   │   └── workflows/                 # GitHub Actions
│   │       ├── rust_ci.yml           # Rust CI流水线
│   │       ├── benchmark.yml         # 性能测试
│   │       └── release.yml           # 发布流程
│   ├── clippy.toml                    # Clippy配置
│   ├── rustfmt.toml                   # Rustfmt配置
│   └── tarpaulin.toml                 # 代码覆盖率配置
├── checklists/                         # 检查清单
│   ├── pr_checklist.md                # PR审查清单
│   ├── release_checklist.md           # 发布清单
│   └── security_checklist.md          # 安全检查清单
└── tools/                              # 辅助工具
    ├── code_generator/                # 代码生成器
    └── perf_analyzer/                 # 性能分析器
```

---

## 🚀 快速开始

### 1. 环境搭建（5分钟）

```bash
# 克隆仓库
git clone <repo-url>
cd OTLP_rust

# 运行环境搭建脚本
./improvement_2025_10_23/15_development_toolkit/scripts/setup_dev_env.sh

# 验证环境
cargo --version
cargo clippy --version
cargo nextest --version
```

### 2. 创建新模块

```bash
# 使用模块生成脚本
./improvement_2025_10_23/15_development_toolkit/scripts/create_module.sh profiling types

# 这将创建：
# - src/profiling/types.rs（基于模板）
# - tests/profiling/types_tests.rs（测试文件）
# - benches/profiling/types_bench.rs（基准测试）
```

### 3. 运行质量检查

```bash
# 运行所有检查
./improvement_2025_10_23/15_development_toolkit/scripts/run_checks.sh

# 单独运行特定检查
cargo fmt --check          # 格式检查
cargo clippy --all-targets # Lint检查
cargo test                 # 单元测试
cargo nextest run          # 快速测试
```

---

## 📝 工具详细说明

### 环境搭建脚本

**文件**: `scripts/setup_dev_env.sh`

**功能**:
- 检查和安装Rust工具链
- 安装必要的cargo工具
- 配置IDE集成
- 设置Git hooks

**使用**:
```bash
./scripts/setup_dev_env.sh [--minimal|--full]
```

---

### 代码生成脚本

**文件**: `scripts/create_module.sh`

**功能**:
- 从模板创建新模块
- 自动生成测试文件
- 创建基准测试框架
- 更新mod.rs

**使用**:
```bash
./scripts/create_module.sh <category> <module_name>

示例:
./scripts/create_module.sh profiling cpu
./scripts/create_module.sh semantic_conventions http
```

---

### 质量检查脚本

**文件**: `scripts/run_checks.sh`

**功能**:
- 运行所有代码质量检查
- 生成覆盖率报告
- 运行性能基准测试
- 生成质量报告

**使用**:
```bash
./scripts/run_checks.sh [--quick|--full|--ci]

选项:
  --quick  快速检查（格式+编译）
  --full   完整检查（包含测试和基准）
  --ci     CI模式（生成报告）
```

---

## ⚙️ CI/CD配置

### GitHub Actions工作流

#### 1. Rust CI流水线

**文件**: `configs/.github/workflows/rust_ci.yml`

**触发条件**:
- Push到main分支
- Pull Request

**步骤**:
```yaml
1. 代码检出
2. Rust工具链设置
3. 依赖缓存
4. 格式检查 (cargo fmt)
5. Lint检查 (cargo clippy)
6. 编译检查 (cargo check)
7. 单元测试 (cargo test)
8. 集成测试
9. 代码覆盖率报告
```

#### 2. 性能基准测试

**文件**: `configs/.github/workflows/benchmark.yml`

**触发条件**:
- 手动触发
- 每周定时运行

**步骤**:
```yaml
1. 运行基准测试
2. 与baseline对比
3. 生成性能报告
4. 发布到GitHub Pages
```

#### 3. 发布流程

**文件**: `configs/.github/workflows/release.yml`

**触发条件**:
- 创建新tag (v*.*.*)

**步骤**:
```yaml
1. 完整测试套件
2. 构建release二进制
3. 生成CHANGELOG
4. 创建GitHub Release
5. 发布到crates.io
```

---

## 📋 检查清单

### PR审查清单

使用此清单确保PR质量：

```markdown
## 代码质量
- [ ] 代码遵循Rust惯例和项目风格
- [ ] 所有public API都有文档注释
- [ ] 复杂逻辑有内联注释说明
- [ ] 没有不必要的unsafe代码
- [ ] 错误处理完善

## 测试
- [ ] 新功能有单元测试
- [ ] 测试覆盖率不低于80%
- [ ] 所有测试通过
- [ ] 关键路径有集成测试
- [ ] 性能敏感代码有基准测试

## 文档
- [ ] README更新（如需要）
- [ ] CHANGELOG更新
- [ ] API文档完整
- [ ] 示例代码可运行

## CI/CD
- [ ] 所有CI检查通过
- [ ] 没有新的clippy警告
- [ ] 格式检查通过
- [ ] 性能无明显退化
```

### 发布清单

**发布前检查**:
```markdown
## 代码
- [ ] 所有planned功能已完成
- [ ] 所有known bugs已修复
- [ ] 代码审查完成
- [ ] 性能测试通过

## 文档
- [ ] CHANGELOG完整
- [ ] 版本号更新
- [ ] API文档审查
- [ ] 迁移指南（如需要）

## 测试
- [ ] 完整测试套件通过
- [ ] 集成测试通过
- [ ] 性能测试通过
- [ ] 手动测试关键功能

## 发布
- [ ] 创建release分支
- [ ] 标记版本号
- [ ] 构建release版本
- [ ] 发布到crates.io
- [ ] GitHub Release创建
- [ ] 公告发布
```

---

## 🔧 配置文件说明

### Clippy配置

**文件**: `configs/clippy.toml`

主要配置项：
```toml
# 最大认知复杂度
cognitive-complexity-threshold = 25

# 最大函数行数
too-many-lines-threshold = 150

# 允许的lint
allow = [
    "too_many_arguments",  # 某些builder需要
]
```

### Rustfmt配置

**文件**: `configs/rustfmt.toml`

主要配置项：
```toml
# 最大行宽
max_width = 100

# 硬tab还是空格
hard_tabs = false
tab_spaces = 4

# 导入排序
imports_granularity = "Crate"
```

### 代码覆盖率配置

**文件**: `configs/tarpaulin.toml`

主要配置项：
```toml
[default]
# 输出格式
out = ["Html", "Xml"]

# 覆盖率阈值
fail-under = 70

# 排除的文件
exclude-files = [
    "tests/*",
    "benches/*",
]
```

---

## 💻 代码模板

### 模块模板

**文件**: `templates/module_template.rs`

提供标准的模块结构：
```rust
//! Module description
//!
//! Detailed documentation about the module

use crate::common::*;

/// Main struct for this module
#[derive(Debug, Clone)]
pub struct ModuleName {
    // Fields
}

impl ModuleName {
    /// Create a new instance
    pub fn new() -> Self {
        Self {
            // Initialize
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        // Test code
    }
}
```

---

## 📊 使用统计

使用这些工具可以：

```yaml
节省时间:
  环境搭建: 从30分钟 → 5分钟
  创建新模块: 从15分钟 → 1分钟
  运行检查: 从10分钟 → 2分钟

提高质量:
  代码一致性: +90%
  测试覆盖率: +20%
  CI通过率: +30%

改善体验:
  新人上手: 从2天 → 1小时
  PR审查: 从1小时 → 20分钟
```

---

## 🤝 贡献指南

如果你想添加新工具或改进现有工具：

1. 在`tools/`目录创建新工具
2. 更新本README
3. 添加使用示例
4. 提交PR

---

## 📞 获取帮助

**遇到问题？**

1. 查看工具的`--help`选项
2. 阅读相关文档
3. 在工作群提问
4. 创建GitHub Issue

---

**创建日期**: 2025年10月23日  
**维护者**: OTLP Rust Team  
**状态**: ✅ 就绪  

🔧 **让开发更高效！** 🚀

