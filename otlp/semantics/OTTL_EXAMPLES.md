# OTTL实践示例集

> **版本**: 2.0  
> **日期**: 2025年10月17日  
> **状态**: ✅ 完整版

---

## 📋 文档概述

本文档提供OTTL（OpenTelemetry Transformation Language）的实践示例集合，覆盖常见使用场景。

完整的OTTL参考请查看：[OTTL_COMPLETE_REFERENCE.md](./OTTL_COMPLETE_REFERENCE.md)

---

## 🔐 数据脱敏示例

### 示例1: PII哈希脱敏

```yaml
processors:
  transform/sanitize_pii:
    error_mode: ignore
    trace_statements:
      - context: span
        statements:
          # 脱敏邮箱
          - set(attributes["user.email"], SHA256(attributes["user.email"])) 
            where attributes["user.email"] != nil
          
          # 脱敏电话
          - set(attributes["user.phone"], SHA256(attributes["user.phone"])) 
            where attributes["user.phone"] != nil
          
          # 脱敏信用卡（保留后4位）
          - set(attributes["payment.card"], Concat("****-****-****-", Substring(attributes["payment.card"], -4, 4)))
            where attributes["payment.card"] != nil
```

### 示例2: SQL语句脱敏

```yaml
processors:
  transform/sanitize_sql:
    error_mode: ignore
    trace_statements:
      - context: span
        statements:
          # 移除SQL中的敏感值
          - replace_pattern(attributes["db.statement"], "password\\s*=\\s*'[^']*'", "password='***'")
          - replace_pattern(attributes["db.statement"], "token\\s*=\\s*'[^']*'", "token='***'")
```

---

## 📉 降维与聚合示例

### 示例3: 高基数属性过滤

```yaml
processors:
  transform/dimension_reduction:
    error_mode: ignore
    metric_statements:
      - context: datapoint
        statements:
          # 只保留关键属性
          - keep_keys(attributes, ["service.name", "deployment.environment", "http.method", "http.status_code"])
    
    trace_statements:
      - context: span
        statements:
          # 删除高基数属性
          - delete_key(attributes, "user.id")
          - delete_key(attributes, "request.id")
          - delete_key(attributes, "session.id")
```

### 示例4: HTTP路由参数化

```yaml
processors:
  transform/parameterize_routes:
    error_mode: ignore
    trace_statements:
      - context: span
        statements:
          # /users/123 -> /users/{id}
          - replace_pattern(attributes["http.route"], "/users/\\d+", "/users/{id}")
          
          # /orders/abc-def-123 -> /orders/{order_id}
          - replace_pattern(attributes["http.route"], "/orders/[a-z0-9-]+", "/orders/{order_id}")
```

---

## 🏷️ 数据标记与增强示例

### 示例5: 异常检测标记

```yaml
processors:
  transform/mark_anomaly:
    error_mode: ignore
    trace_statements:
      - context: span
        statements:
          # 标记超时
          - set(attributes["anomaly.type"], "timeout") 
            where duration > Duration("3s")
          
          # 标记错误
          - set(attributes["anomaly.type"], "error") 
            where status.code == STATUS_CODE_ERROR
          
          # 标记慢查询
          - set(attributes["anomaly.type"], "slow_db") 
            where attributes["db.statement"] != nil and duration > Duration("1s")
```

### 示例6: 环境标记

```yaml
processors:
  transform/enrich_environment:
    error_mode: ignore
    trace_statements:
      - context: resource
        statements:
          # 添加区域信息
          - set(attributes["deployment.region"], "us-west") 
            where attributes["cloud.availability_zone"] matches "us-west-.*"
          
          # 添加环境标签
          - set(attributes["deployment.environment"], "production") 
            where attributes["service.namespace"] == "prod"
```

---

## 🔀 多租户路由示例

### 示例7: 租户标记

```yaml
processors:
  transform/tag_tenant:
    error_mode: ignore
    trace_statements:
      - context: span
        statements:
          # 从Resource提取租户
          - set(attributes["tenant.id"], resource.attributes["tenant.id"])
          
          # 从HTTP头提取租户
          - set(attributes["tenant.id"], attributes["http.request.header.x-tenant-id"])
            where attributes["tenant.id"] == nil
```

### 示例8: 按租户分流（配合routing processor）

```yaml
processors:
  transform/route_prep:
    trace_statements:
      - context: span
        statements:
          - set(attributes["routing_key"], attributes["tenant.id"])
  
  routing:
    from_attribute: routing_key
    table:
      - value: tenant-a
        exporters: [otlp/tenant-a]
      - value: tenant-b
        exporters: [otlp/tenant-b]
    default_exporters: [otlp/default]
```

---

## ⏱️ 采样与过滤示例

### 示例9: 基于延迟的采样

```yaml
processors:
  transform/sampling_prep:
    trace_statements:
      - context: span
        statements:
          # 标记慢请求（总是保留）
          - set(attributes["sample.keep"], true) 
            where duration > Duration("500ms")
          
          # 标记错误（总是保留）
          - set(attributes["sample.keep"], true) 
            where status.code == STATUS_CODE_ERROR

  # 配合tailsampling使用
  tail_sampling:
    policies:
      - name: keep_marked
        type: string_attribute
        string_attribute:
          key: sample.keep
          values: ["true"]
      - name: rate_limited
        type: rate_limiting
        rate_limiting:
          spans_per_second: 100
```

### 示例10: 噪音过滤

```yaml
processors:
  transform/filter_noise:
    error_mode: ignore
    trace_statements:
      - context: span
        statements:
          # 删除健康检查span
          - drop() 
            where attributes["http.route"] == "/health"
          
          # 删除metrics采集span
          - drop() 
            where attributes["http.route"] == "/metrics"
```

---

## 🔧 数据修复示例

### 示例11: 属性规范化

```yaml
processors:
  transform/normalize:
    error_mode: ignore
    trace_statements:
      - context: span
        statements:
          # HTTP method大写
          - set(attributes["http.method"], ConvertCase(attributes["http.method"], "upper"))
          
          # 状态码转数字
          - set(attributes["http.status_code"], Int(attributes["http.status_code"]))
            where IsString(attributes["http.status_code"])
          
          # 添加默认值
          - set(attributes["http.scheme"], "http")
            where attributes["http.scheme"] == nil
```

### 示例12: 错误分类

```yaml
processors:
  transform/classify_errors:
    trace_statements:
      - context: span
        statements:
          # 客户端错误 (4xx)
          - set(attributes["error.category"], "client_error")
            where attributes["http.status_code"] >= 400 and attributes["http.status_code"] < 500
          
          # 服务器错误 (5xx)
          - set(attributes["error.category"], "server_error")
            where attributes["http.status_code"] >= 500
          
          # 超时错误
          - set(attributes["error.category"], "timeout")
            where attributes["error.type"] == "TimeoutException"
```

---

## 💰 成本优化示例

### 示例13: 动态采样率

```yaml
processors:
  transform/dynamic_sampling:
    trace_statements:
      - context: span
        statements:
          # 生产环境低采样
          - set(attributes["sample.rate"], 0.01)
            where resource.attributes["deployment.environment"] == "production"
          
          # 开发环境高采样
          - set(attributes["sample.rate"], 1.0)
            where resource.attributes["deployment.environment"] == "development"
```

### 示例14: Metrics聚合

```yaml
processors:
  transform/aggregate_metrics:
    metric_statements:
      - context: metric
        statements:
          # 删除实例级别标签，只保留服务级别
          - delete_key(attributes, "service.instance.id")
          - delete_key(attributes, "host.name")
```

---

## 🌍 跨信号关联示例

### 示例15: Trace与Log关联

```yaml
processors:
  transform/trace_log_correlation:
    log_statements:
      - context: log
        statements:
          # 从Trace Context提取信息
          - set(attributes["trace_id"], trace_id.string)
          - set(attributes["span_id"], span_id.string)
    
    trace_statements:
      - context: span
        statements:
          # 确保Span有service.name
          - set(resource.attributes["service.name"], "unknown")
            where resource.attributes["service.name"] == nil
```

---

## 🧪 调试与测试示例

### 示例16: 调试标记

```yaml
processors:
  transform/debug:
    error_mode: ignore
    trace_statements:
      - context: span
        statements:
          # 添加调试时间戳
          - set(attributes["debug.processed_at"], Time())
          
          # 添加处理标记
          - set(attributes["debug.ottl_version"], "1.0")
          
          # 记录原始值
          - set(attributes["debug.original_duration"], duration)
```

### 示例17: 条件调试

```yaml
processors:
  transform/conditional_debug:
    trace_statements:
      - context: span
        statements:
          # 只对特定服务启用详细日志
          - set(attributes["debug.verbose"], true)
            where resource.attributes["service.name"] == "payment-service"
            and attributes["http.route"] == "/api/payment"
```

---

## 📚 组合使用示例

### 示例18: 完整生产配置

```yaml
processors:
  # 1. 数据修复和规范化
  transform/1_normalize:
    error_mode: ignore
    trace_statements:
      - context: span
        statements:
          - set(attributes["http.method"], ConvertCase(attributes["http.method"], "upper"))
          - replace_pattern(attributes["http.route"], "/users/\\d+", "/users/{id}")
  
  # 2. 数据增强
  transform/2_enrich:
    trace_statements:
      - context: span
        statements:
          - set(attributes["deployment.region"], resource.attributes["cloud.region"])
          - set(attributes["anomaly.type"], "timeout") where duration > Duration("3s")
  
  # 3. 数据脱敏
  transform/3_sanitize:
    trace_statements:
      - context: span
        statements:
          - set(attributes["user.email"], SHA256(attributes["user.email"]))
            where attributes["user.email"] != nil
  
  # 4. 降维
  transform/4_reduce:
    trace_statements:
      - context: span
        statements:
          - delete_key(attributes, "user.id")
          - delete_key(attributes, "request.id")

service:
  pipelines:
    traces:
      processors: [transform/1_normalize, transform/2_enrich, transform/3_sanitize, transform/4_reduce, batch]
```

---

## ⚠️ 最佳实践

### 1. 性能优化

- ✅ 使用`error_mode: ignore`避免单个错误影响整个批次
- ✅ 将简单操作放在前面，复杂操作放在后面
- ✅ 避免在热路径上使用复杂正则表达式
- ✅ 合理使用条件判断减少不必要的处理

### 2. 可维护性

- ✅ 使用清晰的processor命名（如`transform/1_normalize`）
- ✅ 添加注释说明规则目的
- ✅ 分离不同功能到不同的processor
- ✅ 定期审查和清理过期规则

### 3. 可靠性

- ✅ 始终包含`where`条件避免空值错误
- ✅ 使用测试环境充分验证
- ✅ 准备回滚方案
- ✅ 监控规则执行指标

---

## 🔗 相关文档

- **完整参考**: [OTTL_COMPLETE_REFERENCE.md](./OTTL_COMPLETE_REFERENCE.md)
- **规则治理**: [RULES_GOVERNANCE.md](./RULES_GOVERNANCE.md)
- **性能优化**: [PERFORMANCE_OPTIMIZATION_MANUAL.md](./PERFORMANCE_OPTIMIZATION_MANUAL.md)
- **运维手册**: [RUNBOOK.md](./RUNBOOK.md)

---

## 📝 变更历史

| 版本 | 日期 | 说明 |
|------|------|------|
| 2.0 | 2025-10-17 | 完整版发布：扩展为生产级示例集 |
| 1.0 | 2025-09-XX | 初始版本 |

---

**掌握OTTL，实现数据自由转换！** 🔄✨
