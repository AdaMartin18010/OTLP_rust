# 部署运维知识图谱

**版本**: 2.0
**日期**: 2025年10月28日
**状态**: ✅ 完整

---

## 📋 目录

- [部署运维知识图谱](#部署运维知识图谱)
  - [📋 目录](#-目录)
  - [🌐 部署架构全景](#-部署架构全景)
    - [1.1 完整部署架构](#11-完整部署架构)
  - [🔗 运维流程图](#-运维流程图)
  - [🔗 相关资源](#-相关资源)

---

## 🌐 部署架构全景

### 1.1 完整部署架构

```mermaid
graph TB
    subgraph "开发环境"
        DEV[Docker Compose]
    end

    subgraph "测试环境"
        TEST[K8s测试集群]
    end

    subgraph "生产环境"
        K8S[Kubernetes]
        HPA[HorizontalPodAutoscaler]
        SVC[Service]
        ING[Ingress]
    end

    subgraph "服务发现"
        CONSUL[Consul]
        DNS[CoreDNS]
    end

    subgraph "配置管理"
        CM[ConfigMap]
        SEC[Secret]
        ENV[Environment]
    end

    DEV --> TEST
    TEST --> K8S

    K8S --> HPA
    K8S --> SVC
    SVC --> ING

    K8S --> CONSUL
    CONSUL --> DNS

    K8S --> CM
    K8S --> SEC
    CM --> ENV
    SEC --> ENV

    style K8S fill:#bbf,stroke:#333,stroke-width:2px
    style CONSUL fill:#bfb,stroke:#333,stroke-width:2px
    style CM fill:#fbf,stroke:#333,stroke-width:2px
```

---

## 🔗 运维流程图

```
部署流程:
构建Docker镜像
  ↓
推送到Registry
  ↓
部署到K8s
  ↓
配置HPA
  ↓
注册Consul
  ↓
健康检查
  ↓
生产就绪

监控流程:
Metrics收集
  ↓
Prometheus
  ↓
Grafana可视化
  ↓
告警通知
```

---

## 🔗 相关资源

- [核心概念](./CONCEPTS.md) - 部署详解
- [对比矩阵](./COMPARISON_MATRIX.md) - 方案对比

---

**版本**: 2.0
**创建日期**: 2025-10-28

---

> **💡 提示**: 从Docker开始，逐步迁移到Kubernetes生产环境。
