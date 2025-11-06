# OTTL完整参考手册

> **版本**: 1.0
> **日期**: 2025年10月17日
> **状态**: ✅ 完整版

---

## 📋 目录

- [OTTL完整参考手册](#ottl完整参考手册)
  - [📋 目录](#-目录)
  - [第一部分：OTTL概述](#第一部分ottl概述)
    - [1.1 什么是OTTL?](#11-什么是ottl)
      - [核心特性](#核心特性)
      - [应用场景](#应用场景)
    - [1.2 OTTL在Collector中的位置](#12-ottl在collector中的位置)
    - [1.3 支持的信号类型](#13-支持的信号类型)
  - [第二部分：语法完整参考](#第二部分语法完整参考)
    - [2.1 基本语法结构](#21-基本语法结构)
    - [2.2 数据类型](#22-数据类型)
    - [2.3 路径表达式](#23-路径表达式)
      - [Traces上下文](#traces上下文)
      - [Metrics上下文](#metrics上下文)
      - [Logs上下文](#logs上下文)
    - [2.4 运算符](#24-运算符)
      - [比较运算符](#比较运算符)
      - [逻辑运算符](#逻辑运算符)
      - [示例](#示例)
  - [第三部分：函数完整列表](#第三部分函数完整列表)
    - [3.1 字符串函数](#31-字符串函数)
      - [代码示例](#代码示例)
    - [3.2 属性操作函数](#32-属性操作函数)
      - [代码示例1](#代码示例1)
    - [3.3 类型转换函数](#33-类型转换函数)
      - [代码示例2](#代码示例2)
    - [3.4 哈希和加密函数](#34-哈希和加密函数)
      - [代码示例3](#代码示例3)
    - [3.5 时间函数](#35-时间函数)
      - [代码示例4](#代码示例4)
    - [3.6 数学函数](#36-数学函数)
    - [3.7 集合函数](#37-集合函数)
      - [代码示例5](#代码示例5)
    - [3.8 特殊函数](#38-特殊函数)
  - [第四部分: 最佳实践](#第四部分-最佳实践)
    - [4.1 性能优化](#41-性能优化)
      - [4.1.1 最小化转换次数](#411-最小化转换次数)
      - [4.1.2 使用条件过滤](#412-使用条件过滤)
    - [4.2 安全实践](#42-安全实践)
      - [4.2.1 PII脱敏](#421-pii脱敏)
      - [4.2.2 SQL注入防护](#422-sql注入防护)
    - [4.3 高基数治理](#43-高基数治理)
      - [4.3.1 路径参数化](#431-路径参数化)
      - [4.3.2 属性降维](#432-属性降维)
    - [4.4 数据增强](#44-数据增强)
      - [4.4.1 添加环境标签](#441-添加环境标签)
      - [4.4.2 业务标签提取](#442-业务标签提取)
  - [第五部分: 高级用法](#第五部分-高级用法)
    - [5.1 多条件路由](#51-多条件路由)
    - [5.2 动态采样](#52-动态采样)
    - [5.3 级联转换](#53-级联转换)
  - [第六部分: 性能优化](#第六部分-性能优化)
    - [6.1 性能指标](#61-性能指标)
    - [6.2 优化技巧](#62-优化技巧)
      - [6.2.1 避免重复计算](#621-避免重复计算)
      - [6.2.2 使用早期过滤](#622-使用早期过滤)
    - [6.3 性能测试](#63-性能测试)
  - [第七部分: 故障排查](#第七部分-故障排查)
    - [7.1 常见错误](#71-常见错误)
      - [7.1.1 类型错误](#711-类型错误)
      - [7.1.2 空值处理](#712-空值处理)
      - [7.1.3 正则表达式错误](#713-正则表达式错误)
    - [7.2 调试技巧](#72-调试技巧)
      - [7.2.1 启用详细日志](#721-启用详细日志)
      - [7.2.2 添加调试属性](#722-添加调试属性)
    - [7.3 验证配置](#73-验证配置)
  - [📚 参考资源](#-参考资源)
    - [官方文档](#官方文档)
    - [社区资源](#社区资源)
  - [📝 附录](#-附录)
    - [A. OTTL函数速查表](#a-ottl函数速查表)
    - [B. 性能基准](#b-性能基准)

---

## 第一部分：OTTL概述

### 1.1 什么是OTTL?

**OTTL (OpenTelemetry Transformation Language)** 是OpenTelemetry Collector中的数据转换领域特定语言(DSL),用于在遥测数据管道中执行复杂的转换、过滤和增强操作。

#### 核心特性

| 特性 | 说明 |
|------|------|
| **声明式语法** | 类SQL风格,易于理解和维护 |
| **类型安全** | 编译时类型检查,减少运行时错误 |
| **高性能** | 优化的执行引擎,低延迟 |
| **可组合** | 支持函数嵌套和链式调用 |
| **上下文感知** | 根据信号类型(Traces/Metrics/Logs)提供不同的上下文 |

#### 应用场景

```yaml
应用场景:
├── 数据清洗: 删除敏感字段、PII脱敏
├── 数据增强: 添加环境标签、业务属性
├── 数据路由: 基于规则的多后端分发
├── 数据降采样: 高基数治理、成本优化
├── 数据转换: 格式规范化、单位转换
└── 数据过滤: 噪声过滤、采样控制
```

### 1.2 OTTL在Collector中的位置

```text
┌─────────────────────────────────────────────────┐
│              OTLP/Prometheus/Jaeger             │
│                   (Receivers)                   │
└────────────────┬────────────────────────────────┘
                 │
                 ▼
┌─────────────────────────────────────────────────┐
│               Processors Pipeline               │
│  ┌───────────────────────────────────────────┐  │
│  │  1. Attributes Processor (OTTL)          │  │
│  │  2. Transform Processor (OTTL)           │  │
│  │  3. Filter Processor (OTTL)              │  │
│  │  4. Routing Processor (OTTL)             │  │
│  └───────────────────────────────────────────┘  │
└────────────────┬────────────────────────────────┘
                 │
                 ▼
┌─────────────────────────────────────────────────┐
│         Jaeger/Prometheus/OTLP Backend          │
│                   (Exporters)                   │
└─────────────────────────────────────────────────┘
```

### 1.3 支持的信号类型

| 信号类型 | 上下文对象 | 常用字段 |
|---------|-----------|---------|
| **Traces** | `span`, `resource`, `instrumentation_scope` | `name`, `kind`, `status`, `attributes` |
| **Metrics** | `metric`, `datapoint`, `resource` | `name`, `type`, `unit`, `value` |
| **Logs** | `log`, `resource`, `instrumentation_scope` | `body`, `severity`, `attributes` |

---

## 第二部分：语法完整参考

### 2.1 基本语法结构

```ottl
# 条件表达式
<condition> ? <true_statement> : <false_statement>

# 函数调用
function_name(argument1, argument2, ...)

# 路径表达式
resource.attributes["service.name"]
span.name
log.body
```

### 2.2 数据类型

| 类型 | 说明 | 示例 |
|------|------|------|
| **String** | 字符串 | `"hello"`, `'world'` |
| **Int** | 整数 | `42`, `-100` |
| **Float** | 浮点数 | `3.14`, `-0.5` |
| **Bool** | 布尔值 | `true`, `false` |
| **Bytes** | 字节数组 | 用于二进制数据 |
| **Nil** | 空值 | `nil` |
| **Map** | 映射 | `attributes` |
| **Slice** | 切片 | `events` |

### 2.3 路径表达式

#### Traces上下文

```ottl
# Resource
resource.attributes["service.name"]
resource.attributes["deployment.environment"]

# Span
span.name
span.kind
span.status.code
span.status.message
span.attributes["http.method"]
span.attributes["db.statement"]

# InstrumentationScope
instrumentation_scope.name
instrumentation_scope.version
```

#### Metrics上下文

```ottl
# Metric
metric.name
metric.type
metric.unit
metric.description

# DataPoint
datapoint.attributes["host.name"]
datapoint.start_time_unix_nano
datapoint.time_unix_nano

# Value (根据类型不同)
datapoint.value.int        # Gauge/Sum
datapoint.value.double     # Gauge/Sum
datapoint.value.count      # Histogram
datapoint.value.bucket_counts  # Histogram
```

#### Logs上下文

```ottl
# Log Record
log.body
log.severity_text
log.severity_number
log.attributes["http.status_code"]
log.trace_id
log.span_id

# Timestamp
log.time_unix_nano
log.observed_time_unix_nano
```

### 2.4 运算符

#### 比较运算符

```ottl
==  # 等于
!=  # 不等于
<   # 小于
<=  # 小于等于
>   # 大于
>=  # 大于等于
```

#### 逻辑运算符

```ottl
and  # 逻辑与
or   # 逻辑或
not  # 逻辑非
```

#### 示例

```ottl
# 复杂条件
span.attributes["http.status_code"] >= 500 and
  span.kind == SPAN_KIND_SERVER

# 多条件或
resource.attributes["service.name"] == "frontend" or
  resource.attributes["service.name"] == "api-gateway"
```

---

## 第三部分：函数完整列表

### 3.1 字符串函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `Concat(str1, str2, ...)` | 连接字符串 | `Concat(span.name, "-suffix")` |
| `Split(str, delimiter)` | 分割字符串 | `Split(span.name, ".")` |
| `Substring(str, start, len)` | 提取子串 | `Substring(span.name, 0, 5)` |
| `ToLower(str)` | 转小写 | `ToLower(span.name)` |
| `ToUpper(str)` | 转大写 | `ToUpper(resource.attributes["env"])` |
| `Trim(str)` | 去除首尾空格 | `Trim(log.body)` |
| `Replace(str, old, new)` | 替换字符串 | `Replace(span.name, "/", "-")` |
| `ReplacePattern(str, pattern, replacement)` | 正则替换 | `ReplacePattern(span.name, "\\d+", "X")` |

#### 代码示例

```yaml
# Collector配置
processors:
  transform/strings:
    trace_statements:
      - context: span
        statements:
          # 规范化服务名称
          - set(resource.attributes["service.name"],
                ToLower(resource.attributes["service.name"]))

          # 添加前缀
          - set(span.name,
                Concat("api.", span.name))

          # 清理路径中的ID
          - set(span.attributes["http.target"],
                ReplacePattern(
                  span.attributes["http.target"],
                  "/\\d+/",
                  "/{id}/"
                ))
```

### 3.2 属性操作函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `set(path, value)` | 设置值 | `set(span.name, "new-name")` |
| `delete_key(map, key)` | 删除键 | `delete_key(span.attributes, "password")` |
| `delete_matching_keys(map, pattern)` | 删除匹配的键 | `delete_matching_keys(span.attributes, "^temp_.*")` |
| `keep_keys(map, keys)` | 只保留指定键 | `keep_keys(span.attributes, ["http.method", "http.url"])` |
| `truncate_all(map, limit)` | 截断所有值 | `truncate_all(span.attributes, 256)` |

#### 代码示例1

```yaml
processors:
  transform/attributes:
    trace_statements:
      - context: span
        statements:
          # PII脱敏 - 删除敏感字段
          - delete_key(span.attributes, "user.email")
          - delete_key(span.attributes, "user.phone")
          - delete_matching_keys(span.attributes, ".*token.*")

          # 属性白名单 - 只保留允许的属性
          - keep_keys(span.attributes, [
              "http.method",
              "http.status_code",
              "http.url",
              "service.name"
            ])

          # 值截断 - 防止过长
          - truncate_all(span.attributes, 512)
```

### 3.3 类型转换函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `Int(value)` | 转整数 | `Int(span.attributes["count"])` |
| `Double(value)` | 转浮点数 | `Double(span.attributes["latency"])` |
| `String(value)` | 转字符串 | `String(span.status.code)` |
| `Bool(value)` | 转布尔值 | `Bool(span.attributes["is_error"])` |

#### 代码示例2

```yaml
processors:
  transform/types:
    metric_statements:
      - context: datapoint
        statements:
          # 确保属性类型正确
          - set(attributes["port"], Int(attributes["port"]))
          - set(attributes["latency_ms"], Double(attributes["latency_ms"]))
          - set(attributes["success"], Bool(attributes["success"]))
```

### 3.4 哈希和加密函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `SHA256(str)` | SHA256哈希 | `SHA256(span.attributes["user.id"])` |
| `SHA1(str)` | SHA1哈希 | `SHA1(span.attributes["email"])` |
| `FNV(str)` | FNV哈希 | `FNV(span.attributes["ip"])` |

#### 代码示例3

```yaml
processors:
  transform/hash:
    trace_statements:
      - context: span
        statements:
          # PII哈希化
          - set(span.attributes["user.id_hash"],
                SHA256(span.attributes["user.id"]))
          - delete_key(span.attributes, "user.id")

          - set(span.attributes["email_hash"],
                SHA256(span.attributes["email"]))
          - delete_key(span.attributes, "email")
```

### 3.5 时间函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `Now()` | 当前时间(纳秒) | `Now()` |
| `UnixMilli(timestamp)` | 转毫秒 | `UnixMilli(span.start_time_unix_nano)` |
| `Duration(str)` | 解析时间间隔 | `Duration("5m")` |

#### 代码示例4

```yaml
processors:
  transform/time:
    trace_statements:
      - context: span
        statements:
          # 添加处理时间戳
          - set(span.attributes["processed_at"], Now())

          # 计算延迟(毫秒)
          - set(span.attributes["latency_ms"],
                UnixMilli(span.end_time_unix_nano - span.start_time_unix_nano))
```

### 3.6 数学函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `Min(a, b)` | 最小值 | `Min(datapoint.value, 100)` |
| `Max(a, b)` | 最大值 | `Max(datapoint.value, 0)` |
| `Abs(x)` | 绝对值 | `Abs(datapoint.value)` |
| `Ceil(x)` | 向上取整 | `Ceil(datapoint.value)` |
| `Floor(x)` | 向下取整 | `Floor(datapoint.value)` |

### 3.7 集合函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `IsMatch(str, pattern)` | 正则匹配 | `IsMatch(span.name, "^GET /api/.*")` |
| `IsString(value)` | 是否为字符串 | `IsString(span.attributes["key"])` |
| `IsInt(value)` | 是否为整数 | `IsInt(span.attributes["count"])` |
| `IsBool(value)` | 是否为布尔值 | `IsBool(span.attributes["flag"])` |
| `IsMap(value)` | 是否为映射 | `IsMap(span.attributes)` |

#### 代码示例5

```yaml
processors:
  transform/validation:
    trace_statements:
      - context: span
        statements:
          # 条件验证和转换
          - set(span.attributes["http.status_code"],
                IsInt(span.attributes["http.status_code"]) ?
                  span.attributes["http.status_code"] :
                  Int(span.attributes["http.status_code"]))
```

### 3.8 特殊函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `ParseJSON(str)` | 解析JSON | `ParseJSON(log.body)` |
| `ExtractPatterns(str, pattern)` | 提取模式 | `ExtractPatterns(span.name, "(\\w+)")` |
| `TraceID(bytes)` | 生成TraceID | `TraceID(span.trace_id)` |
| `SpanID(bytes)` | 生成SpanID | `SpanID(span.span_id)` |

---

## 第四部分: 最佳实践

### 4.1 性能优化

#### 4.1.1 最小化转换次数

```yaml
# ❌ 不好 - 多次转换
processors:
  transform/step1:
    trace_statements:
      - context: span
        statements:
          - set(span.name, ToLower(span.name))

  transform/step2:
    trace_statements:
      - context: span
        statements:
          - set(span.name, Concat("api.", span.name))

# ✅ 好 - 合并转换
processors:
  transform/combined:
    trace_statements:
      - context: span
        statements:
          - set(span.name, Concat("api.", ToLower(span.name)))
```

#### 4.1.2 使用条件过滤

```yaml
# ✅ 先过滤再转换
processors:
  transform/optimized:
    trace_statements:
      - context: span
        statements:
          # 只处理需要的span
          - set(span.attributes["normalized_status"],
                span.attributes["http.status_code"] >= 500 ? "error" : "ok")
            where span.kind == SPAN_KIND_SERVER
```

### 4.2 安全实践

#### 4.2.1 PII脱敏

```yaml
processors:
  transform/pii:
    trace_statements:
      - context: span
        statements:
          # 删除敏感字段
          - delete_matching_keys(span.attributes, ".*password.*")
          - delete_matching_keys(span.attributes, ".*token.*")
          - delete_matching_keys(span.attributes, ".*secret.*")

          # 哈希化用户标识
          - set(span.attributes["user.id"],
                SHA256(span.attributes["user.id"]))
            where span.attributes["user.id"] != nil

          # 掩码处理
          - set(span.attributes["credit_card"],
                Concat("****-****-****-",
                       Substring(span.attributes["credit_card"], -4, 4)))
            where span.attributes["credit_card"] != nil
```

#### 4.2.2 SQL注入防护

```yaml
processors:
  transform/sql_sanitize:
    trace_statements:
      - context: span
        statements:
          # 截断过长的SQL语句
          - truncate_all(span.attributes, 4096)
            where span.attributes["db.statement"] != nil

          # 删除包含潜在注入的语句
          - delete_key(span.attributes, "db.statement")
            where IsMatch(span.attributes["db.statement"],
                         ".*(DROP|DELETE|TRUNCATE).*")
```

### 4.3 高基数治理

#### 4.3.1 路径参数化

```yaml
processors:
  transform/cardinality:
    trace_statements:
      - context: span
        statements:
          # URL路径参数化
          - set(span.attributes["http.target"],
                ReplacePattern(
                  span.attributes["http.target"],
                  "/users/\\d+",
                  "/users/{id}"
                ))

          - set(span.attributes["http.target"],
                ReplacePattern(
                  span.attributes["http.target"],
                  "/orders/[a-f0-9-]{36}",
                  "/orders/{uuid}"
                ))
```

#### 4.3.2 属性降维

```yaml
processors:
  transform/dimension_reduction:
    metric_statements:
      - context: datapoint
        statements:
          # HTTP状态码分组
          - set(attributes["http.status_class"],
                attributes["http.status_code"] >= 500 ? "5xx" :
                attributes["http.status_code"] >= 400 ? "4xx" :
                attributes["http.status_code"] >= 300 ? "3xx" :
                attributes["http.status_code"] >= 200 ? "2xx" : "1xx")
          - delete_key(attributes, "http.status_code")

          # 删除高基数标签
          - delete_key(attributes, "user.id")
          - delete_key(attributes, "session.id")
```

### 4.4 数据增强

#### 4.4.1 添加环境标签

```yaml
processors:
  transform/enrich:
    trace_statements:
      - context: span
        statements:
          # 添加环境信息
          - set(resource.attributes["deployment.environment"], "production")
          - set(resource.attributes["datacenter"], "us-east-1")
          - set(resource.attributes["cluster"], "k8s-prod-01")

          # 添加处理时间戳
          - set(span.attributes["processed_at"], Now())

          # 添加版本信息
          - set(span.attributes["collector.version"], "v0.89.0")
```

#### 4.4.2 业务标签提取

```yaml
processors:
  transform/business:
    trace_statements:
      - context: span
        statements:
          # 从URL提取租户ID
          - set(span.attributes["tenant.id"],
                ExtractPatterns(
                  span.attributes["http.url"],
                  "/tenants/(\\w+)"
                )[0])
            where IsMatch(span.attributes["http.url"], "/tenants/\\w+")

          # 从header提取业务ID
          - set(span.attributes["business.unit"],
                span.attributes["http.request.header.x-business-unit"])
```

---

## 第五部分: 高级用法

### 5.1 多条件路由

```yaml
processors:
  routing:
    default_exporters: [otlp/default]
    from_attribute: routing_key
    table:
      - value: critical
        exporters: [otlp/critical, otlp/archive]
      - value: normal
        exporters: [otlp/normal]

  transform/routing:
    trace_statements:
      - context: span
        statements:
          # 设置路由键
          - set(span.attributes["routing_key"],
                span.status.code == STATUS_CODE_ERROR and
                span.attributes["http.status_code"] >= 500 ?
                  "critical" : "normal")
```

### 5.2 动态采样

```yaml
processors:
  transform/sampling:
    trace_statements:
      - context: span
        statements:
          # 计算采样决策
          - set(span.attributes["should_sample"],
                # 错误100%采样
                span.status.code == STATUS_CODE_ERROR ? true :
                # 慢请求100%采样
                (span.end_time_unix_nano - span.start_time_unix_nano) > Duration("1s") ? true :
                # 正常请求10%采样
                FNV(TraceID(span.trace_id)) % 10 == 0 ? true : false)

  filter/sampling:
    traces:
      span:
        - span.attributes["should_sample"] == true
```

### 5.3 级联转换

```yaml
processors:
  transform/cascade:
    trace_statements:
      - context: span
        statements:
          # 步骤1: 规范化
          - set(span.name, ToLower(Trim(span.name)))

          # 步骤2: 参数化
          - set(span.name,
                ReplacePattern(span.name, "\\d+", "{id}"))

          # 步骤3: 添加前缀
          - set(span.name,
                Concat(resource.attributes["service.name"], ".", span.name))

          # 步骤4: 计算衍生指标
          - set(span.attributes["latency_ms"],
                (span.end_time_unix_nano - span.start_time_unix_nano) / 1000000)

          - set(span.attributes["is_slow"],
                span.attributes["latency_ms"] > 1000)
```

---

## 第六部分: 性能优化

### 6.1 性能指标

| 指标 | 目标 | 说明 |
|------|------|------|
| **吞吐量** | ≥100k spans/s | 单核处理能力 |
| **延迟(P95)** | <50ms | 转换处理延迟 |
| **CPU使用率** | <40% | 正常负载下 |
| **内存使用** | <500MB | 稳态内存占用 |

### 6.2 优化技巧

#### 6.2.1 避免重复计算

```yaml
# ❌ 不好 - 重复计算
processors:
  transform/bad:
    trace_statements:
      - context: span
        statements:
          - set(span.attributes["normalized_name"], ToLower(span.name))
          - set(span.attributes["prefixed_name"],
                Concat("api.", ToLower(span.name)))  # 重复ToLower

# ✅ 好 - 复用结果
processors:
  transform/good:
    trace_statements:
      - context: span
        statements:
          - set(span.attributes["normalized_name"], ToLower(span.name))
          - set(span.attributes["prefixed_name"],
                Concat("api.", span.attributes["normalized_name"]))
```

#### 6.2.2 使用早期过滤

```yaml
# ✅ 先过滤再处理
processors:
  filter/early:
    traces:
      span:
        # 只保留SERVER和CLIENT span
        - span.kind == SPAN_KIND_SERVER or span.kind == SPAN_KIND_CLIENT

  transform/process:
    trace_statements:
      - context: span
        statements:
          # 这里只处理已过滤的span
          - set(span.attributes["normalized"], ToLower(span.name))
```

### 6.3 性能测试

```yaml
# 压测配置
receivers:
  otlp:
    protocols:
      grpc:
        endpoint: 0.0.0.0:4317

processors:
  transform/benchmark:
    trace_statements:
      - context: span
        statements:
          - set(span.name, ToLower(span.name))
          - delete_matching_keys(span.attributes, ".*temp.*")

exporters:
  logging:
    loglevel: info

  prometheus:
    endpoint: "0.0.0.0:8888"

service:
  telemetry:
    metrics:
      level: detailed
      address: 0.0.0.0:8888

  pipelines:
    traces:
      receivers: [otlp]
      processors: [transform/benchmark]
      exporters: [logging]
```

---

## 第七部分: 故障排查

### 7.1 常见错误

#### 7.1.1 类型错误

```yaml
# ❌ 错误 - 类型不匹配
- set(span.attributes["count"], "123")  # 字符串赋值给整数字段

# ✅ 正确 - 显式类型转换
- set(span.attributes["count"], Int("123"))
```

#### 7.1.2 空值处理

```yaml
# ❌ 错误 - 未检查nil
- set(span.name, ToLower(span.attributes["custom_name"]))

# ✅ 正确 - 检查nil
- set(span.name, ToLower(span.attributes["custom_name"]))
  where span.attributes["custom_name"] != nil
```

#### 7.1.3 正则表达式错误

```yaml
# ❌ 错误 - 未转义特殊字符
- set(span.name, ReplacePattern(span.name, ".", "-"))  # . 匹配任意字符

# ✅ 正确 - 转义特殊字符
- set(span.name, ReplacePattern(span.name, "\\.", "-"))
```

### 7.2 调试技巧

#### 7.2.1 启用详细日志

```yaml
service:
  telemetry:
    logs:
      level: debug  # 启用调试日志
```

#### 7.2.2 添加调试属性

```yaml
processors:
  transform/debug:
    trace_statements:
      - context: span
        statements:
          # 添加调试标记
          - set(span.attributes["debug.original_name"], span.name)
          - set(span.name, ToLower(span.name))
          - set(span.attributes["debug.transformed_name"], span.name)
```

### 7.3 验证配置

```bash
# 验证配置语法
otelcol validate --config=config.yaml

# 测试转换逻辑
otelcol --config=config.yaml --dry-run
```

---

## 📚 参考资源

### 官方文档

- [OTTL语法规范](https://github.com/open-telemetry/opentelemetry-collector-contrib/blob/main/pkg/ottl/README.md)
- [Transform Processor](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor/transformprocessor)
- [Filter Processor](https://github.com/open-telemetry/opentelemetry-collector-contrib/tree/main/processor/filterprocessor)

### 社区资源

- OpenTelemetry Collector贡献指南
- OTTL最佳实践集合
- 性能优化案例

---

## 📝 附录

### A. OTTL函数速查表

| 类别 | 函数 | 说明 |
|------|------|------|
| **字符串** | Concat, Split, Substring, ToLower, ToUpper, Trim, Replace, ReplacePattern | 字符串操作 |
| **属性** | set, delete_key, delete_matching_keys, keep_keys, truncate_all | 属性操作 |
| **类型** | Int, Double, String, Bool | 类型转换 |
| **哈希** | SHA256, SHA1, FNV | 哈希和加密 |
| **时间** | Now, UnixMilli, Duration | 时间处理 |
| **数学** | Min, Max, Abs, Ceil, Floor | 数学运算 |
| **验证** | IsMatch, IsString, IsInt, IsBool, IsMap | 类型验证 |
| **特殊** | ParseJSON, ExtractPatterns, TraceID, SpanID | 特殊功能 |

### B. 性能基准

| 场景 | 吞吐量 | 延迟(P95) | CPU | 内存 |
|------|--------|-----------|-----|------|
| 简单过滤 | 150k/s | 30ms | 25% | 300MB |
| 属性转换 | 100k/s | 45ms | 35% | 400MB |
| 复杂路由 | 80k/s | 60ms | 40% | 500MB |

---

**完整的OTTL参考手册!** 🎓
