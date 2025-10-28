# 技术细节知识图谱

**版本**: 2.0  
**日期**: 2025年10月28日  
**状态**: ✅ 完整

---

## 📋 目录

1. [性能优化技术栈](#1-性能优化技术栈)

---

## 1. 性能优化技术栈

```mermaid
graph TD
    APP[应用层]
    
    APP --> ZC[零拷贝]
    APP --> POOL[对象池]
    APP --> BATCH[批处理]
    APP --> ASYNC[异步IO]
    
    ZC --> PERF[性能提升]
    POOL --> PERF
    BATCH --> PERF
    ASYNC --> PERF
    
    PERF --> PROD[生产就绪]
    
    style APP fill:#bbf
    style PERF fill:#bfb
    style PROD fill:#6f9
```

---

## 🔗 相关资源

- [核心概念](./CONCEPTS.md) - 技术详解
- [对比矩阵](./COMPARISON_MATRIX.md) - 技术对比

---

**版本**: 2.0  
**创建日期**: 2025-10-28
