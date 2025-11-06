# OTLP语义模型快速入门指南

> **5分钟快速了解OTLP语义模型**
> **日期**: 2025年10月17日

---

## 📋 目录

- [OTLP语义模型快速入门指南](#otlp语义模型快速入门指南)
  - [📋 目录](#-目录)
  - [🎯 一分钟概览](#-一分钟概览)
    - [四个支柱](#四个支柱)
  - [📚 文档导航](#-文档导航)
    - [新手入门 → 阅读这些](#新手入门--阅读这些)
    - [系统学习 → 按顺序阅读](#系统学习--按顺序阅读)
  - [🚀 5分钟快速上手](#-5分钟快速上手)
    - [步骤1: 理解核心概念（2分钟）](#步骤1-理解核心概念2分钟)
    - [步骤2: 查看代码示例（2分钟）](#步骤2-查看代码示例2分钟)
    - [步骤3: 理解数据流（1分钟）](#步骤3-理解数据流1分钟)
  - [💡 常见问题](#-常见问题)
    - [Q1: OTLP vs Prometheus vs Jaeger?](#q1-otlp-vs-prometheus-vs-jaeger)
    - [Q2: 什么时候用Traces？什么时候用Metrics？](#q2-什么时候用traces什么时候用metrics)
    - [Q3: 如何开始使用OTLP？](#q3-如何开始使用otlp)
  - [📖 按角色学习](#-按角色学习)
    - [👨‍💼 我是架构师](#-我是架构师)
    - [👨‍💻 我是开发者](#-我是开发者)
    - [🔧 我是运维工程师](#-我是运维工程师)
    - [👨‍🔬 我是研究人员](#-我是研究人员)
  - [🎓 学习路径](#-学习路径)
    - [路径A: 快速实战（1天）](#路径a-快速实战1天)
    - [路径B: 系统学习（1周）](#路径b-系统学习1周)
    - [路径C: 深度研究（1月）](#路径c-深度研究1月)
  - [🔗 外部资源](#-外部资源)
    - [官方文档](#官方文档)
    - [学习资源](#学习资源)
    - [社区](#社区)
  - [✅ 检查清单](#-检查清单)
    - [基础理解](#基础理解)
    - [实践能力](#实践能力)
    - [高级应用](#高级应用)
  - [🎁 快速参考卡](#-快速参考卡)
    - [Span属性速查](#span属性速查)
    - [Metric类型速查](#metric类型速查)
  - [📞 获取帮助](#-获取帮助)
  - [🎉 下一步](#-下一步)

## 🎯 一分钟概览

**OTLP（OpenTelemetry Protocol）**是云原生可观测性的统一标准。

### 四个支柱

```text
Traces  → 追踪请求路径    → "这个请求慢在哪里？"
Metrics → 统计性能指标    → "CPU使用率是多少？"
Logs    → 记录事件日志    → "发生了什么错误？"
Profiles → 分析性能热点   → "哪段代码最耗CPU？"
```

---

## 📚 文档导航

### 新手入门 → 阅读这些

| 文档 | 用途 | 时长 |
|------|------|------|
| [00_INDEX.md](./00_INDEX.md) | 完整导航 | 5分钟 |
| [README.md](./README.md) | 快速了解 | 3分钟 |
| 本文档 | 立即开始 | 5分钟 |

### 系统学习 → 按顺序阅读

| 序号 | 文档 | 说明 |
|------|------|------|
| 1️⃣ | [01_OTLP语义模型完整定义](./01_OTLP_SEMANTIC_MODEL_COMPLETE.md) | 什么是OTLP（30分钟） |
| 2️⃣ | [02_流模型深度分析](./02_FLOW_ANALYSIS_COMPLETE.md) | 如何分析系统（20分钟） |
| 3️⃣ | [03_标准对标2025](./03_STANDARDS_TRENDS_2025_COMPLETE.md) | 最新技术趋势（30分钟） |

---

## 🚀 5分钟快速上手

### 步骤1: 理解核心概念（2分钟）

**Span（操作片段）**:

```text
一次HTTP请求 = 1个Span
  ↓
调用数据库 = 1个子Span
  ↓
返回结果 = Span结束
```

**Metric（指标）**:

```text
HTTP请求数: Counter（只增不减）
活跃连接数: Gauge（可增可减）
请求延迟: Histogram（分布统计）
```

**Log（日志）**:

```text
[INFO] 用户登录成功
[ERROR] 数据库连接失败
[DEBUG] 调试信息
```

### 步骤2: 查看代码示例（2分钟）

**创建Span**:

```rust
let tracer = global::tracer("my-service");
let mut span = tracer.span_builder("process_order").start(&tracer);

// 做一些工作
process_order().await;

span.end();  // 记录结束时间
```

**记录Metric**:

```rust
let meter = global::meter("my-service");
let counter = meter.u64_counter("http_requests_total").init();

counter.add(1, &[KeyValue::new("method", "GET")]);
```

**记录Log**:

```rust
log::info!("Processing order {}", order_id);
```

### 步骤3: 理解数据流（1分钟）

```text
应用程序 → SDK → Collector → 后端存储 → 查询界面
   ↓        ↓       ↓           ↓          ↓
  生成    缓冲    处理       Jaeger    Grafana
  数据    批量    转换      Prometheus  Kibana
```

---

## 💡 常见问题

### Q1: OTLP vs Prometheus vs Jaeger?

**答**:

- **OTLP**: 统一的传输协议（可以导出到Prometheus和Jaeger）
- **Prometheus**: Metrics存储和查询
- **Jaeger**: Traces存储和查询

### Q2: 什么时候用Traces？什么时候用Metrics？

**答**:

- **Traces**: 追踪具体请求的路径和延迟
- **Metrics**: 统计聚合数据，如QPS、错误率
- **结合使用**: Metrics发现问题 → Traces定位具体请求

### Q3: 如何开始使用OTLP？

**答**:

1. 在代码中添加OpenTelemetry SDK
2. 配置导出到Collector
3. 部署Collector和后端（Jaeger/Prometheus）
4. 在Grafana中查看数据

---

## 📖 按角色学习

### 👨‍💼 我是架构师

**关注点**: 系统设计、技术选型
**推荐阅读**:

1. [01_语义模型](./01_OTLP_SEMANTIC_MODEL_COMPLETE.md) 第1-2章（理解架构）
2. [03_标准对标](./03_STANDARDS_TRENDS_2025_COMPLETE.md) 全文（了解趋势）

### 👨‍💻 我是开发者

**关注点**: 代码实现、API使用
**推荐阅读**:

1. [01_语义模型](./01_OTLP_SEMANTIC_MODEL_COMPLETE.md) 代码示例部分
2. [02_流模型分析](./02_FLOW_ANALYSIS_COMPLETE.md) 实践部分

### 🔧 我是运维工程师

**关注点**: 部署配置、性能优化
**推荐阅读**:

1. [03_标准对标](./03_STANDARDS_TRENDS_2025_COMPLETE.md) 配置章节
2. [MEASUREMENT_GUIDE.md](./MEASUREMENT_GUIDE.md)（指标测量）

### 👨‍🔬 我是研究人员

**关注点**: 理论基础、学术研究
**推荐阅读**:

1. 完整阅读所有文档
2. 参考[理论框架文档](../../docs/02_THEORETICAL_FRAMEWORK/)

---

## 🎓 学习路径

### 路径A: 快速实战（1天）

```text
上午：
├─ 00_INDEX.md（了解结构）
├─ 01_语义模型.md 第1-4章（核心概念）
└─ 代码示例实践

下午：
├─ 03_标准对标.md OTLP章节（配置）
├─ 搭建测试环境
└─ 跑通完整链路
```

### 路径B: 系统学习（1周）

```text
第1-2天：完整阅读01_语义模型
第3-4天：完整阅读02_流模型分析
第5天：  完整阅读03_标准对标
第6天：  实践项目
第7天：  性能测试和优化
```

### 路径C: 深度研究（1月）

```text
第1周：精读所有文档
第2周：对比理论框架
第3周：实现原型系统
第4周：撰写技术报告
```

---

## 🔗 外部资源

### 官方文档

- [OpenTelemetry官网](https://opentelemetry.io/)
- [OTLP规范](https://opentelemetry.io/docs/specs/otlp/)
- [语义约定](https://opentelemetry.io/docs/specs/semconv/)

### 学习资源

- [OpenTelemetry Demo](https://github.com/open-telemetry/opentelemetry-demo)
- [Awesome OpenTelemetry](https://github.com/magsther/awesome-opentelemetry)

### 社区

- [CNCF Slack #opentelemetry](https://cloud-native.slack.com/)
- [GitHub Discussions](https://github.com/open-telemetry/opentelemetry-specification/discussions)

---

## ✅ 检查清单

完成以下任务，确保理解OTLP：

### 基础理解

- [ ] 理解四个支柱的作用
- [ ] 知道Span/Metric/Log的区别
- [ ] 了解OTLP的传输方式

### 实践能力

- [ ] 能编写基本的Trace代码
- [ ] 能配置Collector
- [ ] 能查询和分析数据

### 高级应用

- [ ] 理解语义约定
- [ ] 掌握OTTL转换
- [ ] 了解性能优化方法

---

## 🎁 快速参考卡

### Span属性速查

| 场景 | 属性 | 示例值 |
|------|------|--------|
| HTTP | `http.method` | `GET` |
| HTTP | `http.status_code` | `200` |
| Database | `db.system` | `postgresql` |
| Database | `db.statement` | `SELECT * FROM users` |
| Messaging | `messaging.system` | `kafka` |

### Metric类型速查

| 类型 | 特点 | 场景 |
|------|------|------|
| Counter | 只增不减 | 请求总数 |
| Gauge | 可增可减 | 当前值 |
| Histogram | 分布统计 | 延迟分析 |

---

## 📞 获取帮助

遇到问题？

1. **查文档**: 先看[00_INDEX.md](./00_INDEX.md)
2. **看示例**: 参考具体文档的代码部分
3. **问社区**: CNCF Slack或GitHub Discussions

---

## 🎉 下一步

完成快速入门后，建议：

1. **实践项目**: 在小项目中试用OTLP
2. **深入学习**: 阅读完整文档
3. **参与社区**: 分享经验、贡献代码

---

**开始您的OTLP之旅！** 🚀

**文档版本**: 1.0
**最后更新**: 2025年10月17日
