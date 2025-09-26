# OTTL 規則示例（可直接參考）

> 用於 transformprocessor（contrib）

## 1. 脫敏（示例：HTTP body 哈希）

```yaml
processors:
  transform/sanitize:
    error_mode: ignore
    log_statements:
      - context: log
        statements:
          - set(body, SHA256(body)) where attributes["env"] == "prod"
```

## 2. 降維（保留關鍵屬性）

```yaml
processors:
  transform/dimension_reduction:
    error_mode: ignore
    metric_statements:
      - context: datapoint
        statements:
          - keep_keys(attributes, ["cluster", "node"])  
```

## 3. 標記（超時/錯誤標記）

```yaml
processors:
  transform/mark_timeout:
    error_mode: ignore
    trace_statements:
      - context: span
        statements:
          - set(attributes["anomaly"], "timeout") where duration > 3s
```

## 4. 動態路由（按租戶分流）
>
> 需搭配 `routingprocessor` 或多導出器流水線

```yaml
processors:
  transform/tag_tenant:
    trace_statements:
      - context: span
        statements:
          - set(attributes["tenant"], attributes["resource.tenant"])  
```

## 5. 使用建議

- 先在 PoC 中以小流量灰度，驗證 CPU/RSS/失敗率門檻
- 配合 `RULES_GOVERNANCE.md` 的靜態檢查與回滾流程
