# Profiling快速集成指南

> **版本**: 2.0
> **日期**: 2025年10月17日
> **状态**: ✅ 完整版

---

## 📋 目录

- [Profiling快速集成指南](#profiling快速集成指南)
  - [📋 目录](#-目录)
  - [📋 文档概述](#-文档概述)
  - [🎯 Profiling概述](#-profiling概述)
    - [什么是Profiling](#什么是profiling)
  - [🔧 快速开始](#-快速开始)
    - [1. 后端选择](#1-后端选择)
    - [2. Pyroscope快速部署](#2-pyroscope快速部署)
    - [3. 应用仪表化](#3-应用仪表化)
      - [Go应用](#go应用)
      - [Java应用](#java应用)
      - [Python应用](#python应用)
    - [4. eBPF采集（零代码）](#4-ebpf采集零代码)
  - [🔗 与Traces关联](#-与traces关联)
    - [配置Resource一致性](#配置resource一致性)
    - [Grafana关联查询](#grafana关联查询)
  - [📊 采样策略](#-采样策略)
    - [采样频率建议](#采样频率建议)
    - [动态采样配置](#动态采样配置)
  - [💰 成本评估](#-成本评估)
    - [资源开销](#资源开销)
    - [成本优化建议](#成本优化建议)
  - [🔍 使用场景](#-使用场景)
    - [场景1: 性能热点分析](#场景1-性能热点分析)
    - [场景2: 从Trace跳转到Profile](#场景2-从trace跳转到profile)
    - [场景3: 内存泄漏检测](#场景3-内存泄漏检测)
  - [⚠️ 注意事项](#️-注意事项)
    - [eBPF限制](#ebpf限制)
    - [降级策略](#降级策略)
  - [📚 相关文档](#-相关文档)
  - [📝 变更历史](#-变更历史)

## 📋 文档概述

本文档提供OTLP Profiling（第四支柱）的快速集成指南，包括后端选择、采集方案和最佳实践。

更完整的内容请参考：[PROFILES_INTEGRATION_GUIDE.md](./PROFILES_INTEGRATION_GUIDE.md)

---

## 🎯 Profiling概述

### 什么是Profiling

Profiling是OpenTelemetry的**第四支柱**（Traces/Metrics/Logs/Profiles），用于持续性能分析。

**核心能力**:

- **CPU Profiling**: CPU使用热点分析
- **Memory Profiling**: 内存分配和泄漏检测
- **Off-CPU Profiling**: I/O和锁等待分析
- **与Traces关联**: 从Trace跳转到Profile

---

## 🔧 快速开始

### 1. 后端选择

| 后端 | 优势 | 适用场景 |
|------|------|---------|
| **Pyroscope** | 轻量、易用、开源 | 中小规模、本地部署 |
| **Parca** | 云原生、eBPF支持 | Kubernetes环境 |
| **Elastic APM** | 统一可观测平台 | 已使用Elastic栈 |

### 2. Pyroscope快速部署

**Docker Compose**:

```yaml
# docker-compose.yml
services:
  pyroscope:
    image: pyroscope/pyroscope:latest
    ports:
      - "4040:4040"
    command:
      - "server"
    environment:
      - PYROSCOPE_LOG_LEVEL=debug
    volumes:
      - pyroscope-data:/var/lib/pyroscope

volumes:
  pyroscope-data:
```

**启动**:

```bash
docker-compose up -d pyroscope
# 访问: http://localhost:4040
```

### 3. 应用仪表化

#### Go应用

```go
package main

import (
    "github.com/pyroscope-io/client/pyroscope"
)

func main() {
    pyroscope.Start(pyroscope.Config{
        ApplicationName: "my-app",
        ServerAddress:   "http://pyroscope:4040",

        // CPU profiling
        ProfileTypes: []pyroscope.ProfileType{
            pyroscope.ProfileCPU,
            pyroscope.ProfileAllocObjects,
            pyroscope.ProfileAllocSpace,
            pyroscope.ProfileInuseObjects,
            pyroscope.ProfileInuseSpace,
        },

        // 与OTLP Resource关联
        Tags: map[string]string{
            "env":     "production",
            "region":  "us-west",
            "service": "my-app",
        },
    })

    // 应用代码...
}
```

#### Java应用

```bash
# 添加Java Agent
java -javaagent:pyroscope.jar \
  -Dpyroscope.application.name=my-app \
  -Dpyroscope.server.address=http://pyroscope:4040 \
  -Dpyroscope.format=jfr \
  -jar my-app.jar
```

#### Python应用

```python
import pyroscope

pyroscope.configure(
    application_name="my-app",
    server_address="http://pyroscope:4040",
    tags={
        "env": "production",
        "region": "us-west",
    }
)

# 应用代码...
```

### 4. eBPF采集（零代码）

**部署Pyroscope eBPF Agent**:

```yaml
# k8s-pyroscope-ebpf.yaml
apiVersion: apps/v1
kind: DaemonSet
metadata:
  name: pyroscope-ebpf
  namespace: observability
spec:
  selector:
    matchLabels:
      app: pyroscope-ebpf
  template:
    metadata:
      labels:
        app: pyroscope-ebpf
    spec:
      hostPID: true
      hostNetwork: true
      containers:
      - name: pyroscope-ebpf
        image: pyroscope/pyroscope:latest
        command:
          - "/usr/bin/pyroscope"
          - "ebpf"
          - "--server-address=http://pyroscope:4040"
        securityContext:
          privileged: true
          capabilities:
            add: ["SYS_ADMIN"]
        volumeMounts:
        - name: sys
          mountPath: /sys
          readOnly: true
        - name: debugfs
          mountPath: /sys/kernel/debug
      volumes:
      - name: sys
        hostPath:
          path: /sys
      - name: debugfs
        hostPath:
          path: /sys/kernel/debug
```

---

## 🔗 与Traces关联

### 配置Resource一致性

**确保Traces和Profiles使用相同的Resource属性**:

```yaml
# otel-collector-config.yaml
processors:
  resource:
    attributes:
      - key: service.name
        value: my-app
        action: upsert
      - key: deployment.environment
        value: production
        action: upsert
      - key: service.instance.id
        value: ${HOSTNAME}
        action: upsert
```

### Grafana关联查询

```yaml
# grafana-datasource.yaml
apiVersion: 1
datasources:
  - name: Pyroscope
    type: pyroscope
    url: http://pyroscope:4040

  - name: Tempo
    type: tempo
    url: http://tempo:3200
    jsonData:
      tracesToProfiles:
        datasourceUid: pyroscope
        tags: ['service.name', 'service.instance.id']
```

---

## 📊 采样策略

### 采样频率建议

| 环境 | CPU采样频率 | 说明 |
|------|------------|------|
| **开发** | 100 Hz | 高精度，性能影响可接受 |
| **预生产** | 49 Hz | 平衡精度和开销 |
| **生产** | 9-19 Hz | 低开销，长期运行 |
| **按需** | 100 Hz | 问题排查时临时提高 |

### 动态采样配置

```yaml
# 基于告警动态调整采样频率
sampling:
  default: 19  # 默认19Hz

  on_alert:
    - trigger: high_cpu
      frequency: 100  # CPU异常时提高到100Hz
      duration: 10m

    - trigger: high_latency
      frequency: 49
      duration: 15m
```

---

## 💰 成本评估

### 资源开销

| 指标 | 目标 | 实测（19Hz） |
|------|------|-------------|
| **CPU开销** | <5% | ~2% |
| **内存开销** | <100MB | ~50MB |
| **带宽** | <200KB/s/节点 | ~150KB/s |
| **存储** | 根据保留期 | ~10GB/节点/月 |

### 成本优化建议

1. **降低采样频率**: 9-19Hz已满足大多数场景
2. **按需采样**: 正常时低频，告警时提频
3. **数据保留策略**: 7-30天，根据需求调整
4. **选择性采集**: 只对关键服务启用

---

## 🔍 使用场景

### 场景1: 性能热点分析

```bash
# 1. 在Pyroscope UI查看火焰图
# 2. 识别CPU占用最高的函数
# 3. 点击函数查看调用栈
# 4. 优化热点代码
```

### 场景2: 从Trace跳转到Profile

```bash
# 1. 在Jaeger/Tempo中发现慢Span
# 2. 点击"View in Pyroscope"链接
# 3. 查看该时间段的Profile
# 4. 分析性能瓶颈
```

### 场景3: 内存泄漏检测

```bash
# 1. 查看Memory Profiling（Heap Inuse）
# 2. 对比不同时间点的内存快照
# 3. 识别持续增长的对象
# 4. 定位泄漏代码路径
```

---

## ⚠️ 注意事项

### eBPF限制

- **内核版本**: 需要Linux 4.9+（推荐5.8+）
- **权限要求**: 需要`CAP_SYS_ADMIN`或`CAP_BPF`
- **容器环境**: 需要`hostPID`和`privileged`模式
- **云环境**: 某些托管Kubernetes可能不支持

### 降级策略

```yaml
# 如果eBPF不可用，降级到push方式
fallback_strategy:
  - method: ebpf
    priority: 1
  - method: push
    priority: 2
  - method: pull
    priority: 3
```

---

## 📚 相关文档

- **完整指南**: [PROFILES_INTEGRATION_GUIDE.md](./PROFILES_INTEGRATION_GUIDE.md)
- **eBPF实践**: [EBPF_PRACTICE_GUIDE.md](./EBPF_PRACTICE_GUIDE.md)
- **性能优化**: [PERFORMANCE_OPTIMIZATION_MANUAL.md](./PERFORMANCE_OPTIMIZATION_MANUAL.md)
- **标准趋势**: [03_STANDARDS_TRENDS_2025_COMPLETE.md](./03_STANDARDS_TRENDS_2025_COMPLETE.md)

---

## 📝 变更历史

| 版本 | 日期 | 说明 |
|------|------|------|
| 2.0 | 2025-10-17 | 完整版发布：扩展为快速集成指南 |
| 1.0 | 2025-09-XX | 初始版本 |

---

**快速集成Profiling，实现持续性能优化！** 🔥✨
