# eBPF TODO 清理计划 2025

**创建日期**: 2025年1月
**状态**: 📋 计划中
**Rust 版本**: 1.92+

---

## 📋 执行摘要

本文档列出 eBPF 模块中所有 TODO 注释，并提供清理计划。

---

## 📊 TODO 统计

### 总体统计

- **TODO 总数**: 33 个
- **涉及文件**: 8 个
- **优先级**: 高 (需要实际 eBPF 程序集成)

---

## 📝 TODO 列表

### 1. loader.rs (6 个 TODO)

#### 1.1 程序加载
- **位置**: `load()` 方法
- **内容**: `// TODO: 使用 aya 加载 eBPF 程序`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: aya crate 集成

#### 1.2 系统支持检查
- **位置**: `check_system_support()` 方法
- **内容**:
  - `// TODO: 检查内核版本 >= 5.8`
  - `// TODO: 检查 BTF 支持`
  - `// TODO: 检查 CAP_BPF 权限`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: 系统调用、文件系统检查

#### 1.3 程序验证
- **位置**: `validate_program()` 方法
- **内容**: `// TODO: 使用 object crate 验证 eBPF 程序格式`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: object crate 集成

#### 1.4 程序卸载
- **位置**: `unload()` 方法
- **内容**: `// TODO: 卸载 eBPF 程序`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: aya crate 集成

---

### 2. probes.rs (4 个 TODO)

#### 2.1 KProbe 附加
- **位置**: `attach_kprobe()` 方法
- **内容**: `// TODO: 使用 aya 附加 kprobe`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: aya crate 集成

#### 2.2 UProbe 附加
- **位置**: `attach_uprobe()` 方法
- **内容**: `// TODO: 使用 aya 附加 uprobe`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: aya crate 集成

#### 2.3 Tracepoint 附加
- **位置**: `attach_tracepoint()` 方法
- **内容**: `// TODO: 使用 aya 附加 tracepoint`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: aya crate 集成

#### 2.4 探针分离
- **位置**: `detach()` 和 `detach_all()` 方法
- **内容**:
  - `// TODO: 分离指定探针`
  - `// TODO: 分离所有探针`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: aya crate 集成

---

### 3. events.rs (1 个 TODO)

#### 3.1 事件处理
- **位置**: `process_event()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: 事件处理逻辑完善

---

### 4. maps.rs (3 个 TODO)

#### 4.1 Map 读取
- **位置**: `read_map()` 方法
- **内容**: `// TODO: 使用 aya 读取 Map`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: aya crate 集成

#### 4.2 Map 写入
- **位置**: `write_map()` 方法
- **内容**: `// TODO: 使用 aya 写入 Map`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: aya crate 集成

#### 4.3 Map 删除
- **位置**: `delete_map()` 方法
- **内容**: `// TODO: 使用 aya 删除 Map 中的键值对`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: aya crate 集成

---

### 5. profiling.rs (5 个 TODO)

#### 5.1 启动采样
- **位置**: `start()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: eBPF 程序加载和探针附加

#### 5.2 停止采样
- **位置**: `stop()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: 数据收集和转换

#### 5.3 开销测量
- **位置**: `get_overhead()` 方法
- **内容**: `// TODO: 实际实现需要测量 CPU 和内存使用`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: 性能监控工具

#### 5.4 暂停采样
- **位置**: `pause()` 方法
- **内容**: `// TODO: 实际实现需要暂停采样`
- **优先级**: 低
- **状态**: 待实现
- **依赖**: eBPF 程序控制

#### 5.5 恢复采样
- **位置**: `resume()` 方法
- **内容**: `// TODO: 实际实现需要恢复采样`
- **优先级**: 低
- **状态**: 待实现
- **依赖**: eBPF 程序控制

---

### 6. networking.rs (3 个 TODO)

#### 6.1 启动追踪
- **位置**: `start()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: eBPF 程序加载和探针附加

#### 6.2 停止追踪
- **位置**: `stop()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: 数据收集和转换

#### 6.3 统计信息
- **位置**: `get_stats()` 方法
- **内容**: `// TODO: 实际实现需要从 eBPF Maps 读取统计信息`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: Maps 读取功能

---

### 7. syscalls.rs (4 个 TODO)

#### 7.1 启动追踪
- **位置**: `start()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: eBPF 程序加载和探针附加

#### 7.2 停止追踪
- **位置**: `stop()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: 数据收集和转换

#### 7.3 统计信息
- **位置**: `get_stats()` 方法
- **内容**: `// TODO: 实际实现需要从 eBPF Maps 读取统计信息`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: Maps 读取功能

#### 7.4 系统调用过滤
- **位置**: `filter_syscall()` 方法
- **内容**: `// TODO: 实际实现需要更新 eBPF 程序过滤规则`
- **优先级**: 低
- **状态**: 待实现
- **依赖**: eBPF 程序动态更新

---

### 8. memory.rs (3 个 TODO)

#### 8.1 启动追踪
- **位置**: `start()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: eBPF 程序加载和探针附加

#### 8.2 停止追踪
- **位置**: `stop()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 高
- **状态**: 待实现
- **依赖**: 数据收集和转换

#### 8.3 统计信息
- **位置**: `get_stats()` 方法
- **内容**: `// TODO: 实际实现需要从 eBPF Maps 读取统计信息`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: Maps 读取功能

---

### 9. integration.rs (3 个 TODO)

#### 9.1 事件到 Span 转换
- **位置**: `convert_event_to_span()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: OpenTelemetry API 完善

#### 9.2 事件到 Metric 转换
- **位置**: `convert_event_to_metric()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: OpenTelemetry API 完善

#### 9.3 Profile 到 OTLP 转换
- **位置**: `convert_profile_to_otlp()` 方法
- **内容**: `// TODO: 实际实现需要:`
- **优先级**: 中
- **状态**: 待实现
- **依赖**: OTLP Profile 规范

---

## 🎯 清理计划

### Phase 1: 核心功能 (高优先级)

**目标**: 实现基本的 eBPF 程序加载和探针管理

1. **loader.rs**
   - [ ] 实现 `load()` - 使用 aya 加载 eBPF 程序
   - [ ] 实现 `check_system_support()` - 系统支持检查
   - [ ] 实现 `validate_program()` - 程序格式验证
   - [ ] 实现 `unload()` - 程序卸载

2. **probes.rs**
   - [ ] 实现 `attach_kprobe()` - KProbe 附加
   - [ ] 实现 `attach_uprobe()` - UProbe 附加
   - [ ] 实现 `attach_tracepoint()` - Tracepoint 附加
   - [ ] 实现 `detach()` 和 `detach_all()` - 探针分离

3. **maps.rs**
   - [ ] 实现 `read_map()` - Map 读取
   - [ ] 实现 `write_map()` - Map 写入
   - [ ] 实现 `delete_map()` - Map 删除

**预计时间**: 2-3 周

---

### Phase 2: 功能模块 (高优先级)

**目标**: 实现各功能模块的实际数据收集

1. **profiling.rs**
   - [ ] 实现 `start()` - 启动 CPU 采样
   - [ ] 实现 `stop()` - 停止采样并收集数据
   - [ ] 实现 `get_overhead()` - 性能开销测量

2. **networking.rs**
   - [ ] 实现 `start()` - 启动网络追踪
   - [ ] 实现 `stop()` - 停止追踪并收集数据
   - [ ] 实现 `get_stats()` - 统计信息读取

3. **syscalls.rs**
   - [ ] 实现 `start()` - 启动系统调用追踪
   - [ ] 实现 `stop()` - 停止追踪并收集数据
   - [ ] 实现 `get_stats()` - 统计信息读取

4. **memory.rs**
   - [ ] 实现 `start()` - 启动内存追踪
   - [ ] 实现 `stop()` - 停止追踪并收集数据
   - [ ] 实现 `get_stats()` - 统计信息读取

**预计时间**: 3-4 周

---

### Phase 3: 辅助功能 (中低优先级)

**目标**: 完善辅助功能和用户体验

1. **profiling.rs**
   - [ ] 实现 `pause()` - 暂停采样
   - [ ] 实现 `resume()` - 恢复采样

2. **syscalls.rs**
   - [ ] 实现 `filter_syscall()` - 系统调用过滤

3. **events.rs**
   - [ ] 完善 `process_event()` - 事件处理逻辑

4. **integration.rs**
   - [ ] 完善 `convert_event_to_span()` - 事件到 Span 转换
   - [ ] 完善 `convert_event_to_metric()` - 事件到 Metric 转换
   - [ ] 完善 `convert_profile_to_otlp()` - Profile 到 OTLP 转换

**预计时间**: 2-3 周

---

## 📊 优先级矩阵

| 优先级 | 数量 | 模块 |
|--------|------|------|
| 高 | 18 | loader, probes, maps, profiling, networking, syscalls, memory |
| 中 | 12 | profiling (overhead), networking (stats), syscalls (stats), memory (stats), integration |
| 低 | 3 | profiling (pause/resume), syscalls (filter) |

---

## 🚀 实施建议

### 立即开始 (本周)

1. **研究 aya crate 文档**
   - 了解如何加载 eBPF 程序
   - 了解如何附加探针
   - 了解如何操作 Maps

2. **创建 eBPF 程序示例**
   - 简单的 CPU 采样程序
   - 简单的网络追踪程序
   - 简单的系统调用追踪程序

3. **实现 loader.rs 核心功能**
   - 系统支持检查
   - 程序加载
   - 程序验证

### 短期 (2-4周)

1. **实现 probes.rs 和 maps.rs**
2. **实现 profiling.rs 基础功能**
3. **实现 networking.rs 基础功能**

### 中期 (1-2个月)

1. **实现所有功能模块**
2. **完善集成模块**
3. **添加端到端测试**

---

## 📚 参考资源

### 文档

- [aya 文档](https://aya-rs.dev/book/)
- [eBPF 文档](https://ebpf.io/what-is-ebpf/)
- [OpenTelemetry 规范](https://opentelemetry.io/docs/)

### 示例

- [aya 示例](https://github.com/aya-rs/aya/tree/main/examples)
- [eBPF 示例](https://github.com/iovisor/bcc/tree/master/examples)

---

**状态**: 📋 计划中
**最后更新**: 2025年1月
