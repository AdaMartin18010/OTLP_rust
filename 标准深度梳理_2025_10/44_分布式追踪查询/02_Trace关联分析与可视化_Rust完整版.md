# Trace 关联分析与可视化 - Rust 完整实现

> **文档版本**: v1.0.0  
> **Rust 版本**: 1.90+  
> **最后更新**: 2025-10-10

---

## 📋 目录

- [Trace 关联分析与可视化 - Rust 完整实现](#trace-关联分析与可视化---rust-完整实现)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [核心功能](#核心功能)
    - [应用场景](#应用场景)
  - [🔗 Trace 关联分析](#-trace-关联分析)
    - [1. 调用链路分析](#1-调用链路分析)
    - [2. 关键路径分析](#2-关键路径分析)
    - [3. 瓶颈识别](#3-瓶颈识别)
  - [📊 服务依赖分析](#-服务依赖分析)
    - [1. 服务拓扑图](#1-服务拓扑图)
    - [2. 依赖深度分析](#2-依赖深度分析)
    - [3. 循环依赖检测](#3-循环依赖检测)
  - [⚡ 性能分析](#-性能分析)
    - [1. 耗时分布分析](#1-耗时分布分析)
    - [2. P95/P99 分析](#2-p95p99-分析)
    - [3. 异常检测](#3-异常检测)
  - [🎨 Trace 可视化](#-trace-可视化)
    - [1. 瀑布图生成](#1-瀑布图生成)
    - [2. 火焰图生成](#2-火焰图生成)
    - [3. Gantt 图生成](#3-gantt-图生成)
  - [📈 聚合分析](#-聚合分析)
    - [1. 时间窗口聚合](#1-时间窗口聚合)
    - [2. 服务级别聚合](#2-服务级别聚合)
  - [🔍 根因分析](#-根因分析)
    - [1. 错误传播分析](#1-错误传播分析)
    - [2. 异常根因定位](#2-异常根因定位)
  - [📊 完整示例：Trace 分析平台](#-完整示例trace-分析平台)
  - [🎯 最佳实践](#-最佳实践)
    - [性能优化](#性能优化)
    - [可视化建议](#可视化建议)
    - [分析策略](#分析策略)
  - [📚 参考资源](#-参考资源)

---

## 🎯 概述

Trace 关联分析与可视化是分布式追踪系统的高级功能，通过多维度分析和直观的可视化，帮助开发者快速定位性能瓶颈和故障根因。

### 核心功能

- ✅ **调用链路分析** - 完整的请求调用路径
- ✅ **关键路径识别** - 找出影响性能的关键节点
- ✅ **瓶颈检测** - 自动识别慢查询和资源瓶颈
- ✅ **服务依赖图** - 可视化服务间调用关系
- ✅ **性能分布分析** - 统计分析和异常检测
- ✅ **可视化渲染** - 瀑布图、火焰图、Gantt 图
- ✅ **根因分析** - 错误传播链追踪

### 应用场景

- 🔧 **性能调优** - 识别慢请求和性能热点
- 🔧 **故障排查** - 快速定位错误根因
- 🔧 **容量规划** - 分析服务负载和依赖关系
- 🔧 **架构优化** - 发现冗余调用和循环依赖

---

## 🔗 Trace 关联分析

### 1. 调用链路分析

```rust
use std::sync::Arc;
use std::collections::{HashMap, VecDeque};
use chrono::{DateTime, Utc};

/// 调用链路分析器
pub struct CallChainAnalyzer {
    trace_reconstructor: Arc<TraceReconstructor>,
}

impl CallChainAnalyzer {
    pub fn new(trace_reconstructor: Arc<TraceReconstructor>) -> Self {
        Self { trace_reconstructor }
    }
    
    /// 分析调用链路
    pub async fn analyze_call_chain(
        &self,
        trace_id: &TraceId,
    ) -> Result<CallChainAnalysis, AnalysisError> {
        // 重建 Trace 树
        let trace_tree = self.trace_reconstructor
            .reconstruct_trace_tree(trace_id)
            .await?;
        
        let mut chains = Vec::new();
        
        // 遍历每个根节点
        for root in &trace_tree.root_nodes {
            let chain = self.extract_call_chain(root, Vec::new());
            chains.push(chain);
        }
        
        // 计算总的调用深度
        let max_depth = chains
            .iter()
            .map(|chain| chain.len())
            .max()
            .unwrap_or(0);
        
        // 计算调用总数
        let total_calls = chains
            .iter()
            .map(|chain| chain.len())
            .sum();
        
        Ok(CallChainAnalysis {
            trace_id: *trace_id,
            chains,
            max_depth,
            total_calls,
        })
    }
    
    /// 提取调用链
    fn extract_call_chain(
        &self,
        node: &TraceTreeNode,
        mut current_chain: Vec<CallChainNode>,
    ) -> Vec<CallChainNode> {
        // 添加当前节点
        current_chain.push(CallChainNode {
            span_id: node.span.span_id,
            span_name: node.span.name.clone(),
            service_name: node.span.service_name.clone(),
            start_time: node.span.start_time,
            end_time: node.span.end_time,
            duration_ms: node.span.duration_ms,
            depth: current_chain.len(),
        });
        
        // 递归处理子节点（深度优先）
        if let Some(child) = node.children.first() {
            self.extract_call_chain(child, current_chain)
        } else {
            current_chain
        }
    }
}

#[derive(Debug, Clone)]
pub struct CallChainAnalysis {
    pub trace_id: TraceId,
    pub chains: Vec<Vec<CallChainNode>>,
    pub max_depth: usize,
    pub total_calls: usize,
}

#[derive(Debug, Clone)]
pub struct CallChainNode {
    pub span_id: SpanId,
    pub span_name: String,
    pub service_name: String,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub duration_ms: i64,
    pub depth: usize,
}

pub type TraceId = [u8; 16];
pub type SpanId = [u8; 8];

#[derive(Debug)]
pub enum AnalysisError {
    TraceNotFound,
    ReconstructionFailed(String),
    AnalysisFailed(String),
}
```

---

### 2. 关键路径分析

```rust
/// 关键路径分析器
pub struct CriticalPathAnalyzer {
    call_chain_analyzer: Arc<CallChainAnalyzer>,
}

impl CriticalPathAnalyzer {
    pub fn new(call_chain_analyzer: Arc<CallChainAnalyzer>) -> Self {
        Self { call_chain_analyzer }
    }
    
    /// 识别关键路径（最长耗时路径）
    pub async fn find_critical_path(
        &self,
        trace_id: &TraceId,
    ) -> Result<CriticalPath, AnalysisError> {
        let analysis = self.call_chain_analyzer
            .analyze_call_chain(trace_id)
            .await?;
        
        // 找出耗时最长的链路
        let critical_chain = analysis
            .chains
            .into_iter()
            .max_by_key(|chain| {
                chain.iter().map(|node| node.duration_ms).sum::<i64>()
            })
            .ok_or(AnalysisError::AnalysisFailed("No chains found".to_string()))?;
        
        let total_duration = critical_chain
            .iter()
            .map(|node| node.duration_ms)
            .sum();
        
        // 识别关键节点（耗时超过总时间的 20%）
        let threshold = (total_duration as f64 * 0.2) as i64;
        
        let critical_nodes: Vec<CallChainNode> = critical_chain
            .iter()
            .filter(|node| node.duration_ms >= threshold)
            .cloned()
            .collect();
        
        Ok(CriticalPath {
            trace_id: *trace_id,
            full_chain: critical_chain,
            critical_nodes,
            total_duration,
        })
    }
    
    /// 计算每个 Span 在关键路径中的占比
    pub fn calculate_span_contribution(
        &self,
        critical_path: &CriticalPath,
    ) -> Vec<SpanContribution> {
        let total_duration = critical_path.total_duration as f64;
        
        critical_path
            .full_chain
            .iter()
            .map(|node| {
                let percentage = (node.duration_ms as f64 / total_duration) * 100.0;
                
                SpanContribution {
                    span_id: node.span_id,
                    span_name: node.span_name.clone(),
                    service_name: node.service_name.clone(),
                    duration_ms: node.duration_ms,
                    percentage,
                }
            })
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct CriticalPath {
    pub trace_id: TraceId,
    pub full_chain: Vec<CallChainNode>,
    pub critical_nodes: Vec<CallChainNode>,
    pub total_duration: i64,
}

#[derive(Debug, Clone)]
pub struct SpanContribution {
    pub span_id: SpanId,
    pub span_name: String,
    pub service_name: String,
    pub duration_ms: i64,
    pub percentage: f64,
}
```

---

### 3. 瓶颈识别

```rust
/// 瓶颈识别器
pub struct BottleneckDetector {
    critical_path_analyzer: Arc<CriticalPathAnalyzer>,
}

impl BottleneckDetector {
    pub fn new(critical_path_analyzer: Arc<CriticalPathAnalyzer>) -> Self {
        Self { critical_path_analyzer }
    }
    
    /// 识别性能瓶颈
    pub async fn detect_bottlenecks(
        &self,
        trace_id: &TraceId,
        threshold_percentage: f64, // 例如 20.0 表示占总时间的 20%
    ) -> Result<Vec<Bottleneck>, AnalysisError> {
        let critical_path = self.critical_path_analyzer
            .find_critical_path(trace_id)
            .await?;
        
        let contributions = self.critical_path_analyzer
            .calculate_span_contribution(&critical_path);
        
        let bottlenecks: Vec<Bottleneck> = contributions
            .into_iter()
            .filter(|contrib| contrib.percentage >= threshold_percentage)
            .map(|contrib| {
                // 识别瓶颈类型
                let bottleneck_type = self.classify_bottleneck(&contrib);
                
                Bottleneck {
                    span_id: contrib.span_id,
                    span_name: contrib.span_name,
                    service_name: contrib.service_name,
                    duration_ms: contrib.duration_ms,
                    percentage: contrib.percentage,
                    bottleneck_type,
                }
            })
            .collect();
        
        Ok(bottlenecks)
    }
    
    /// 分类瓶颈类型
    fn classify_bottleneck(&self, contrib: &SpanContribution) -> BottleneckType {
        // 基于 Span 名称推断类型
        let name_lower = contrib.span_name.to_lowercase();
        
        if name_lower.contains("sql") || name_lower.contains("query") || name_lower.contains("database") {
            BottleneckType::Database
        } else if name_lower.contains("http") || name_lower.contains("rpc") || name_lower.contains("grpc") {
            BottleneckType::Network
        } else if name_lower.contains("compute") || name_lower.contains("process") {
            BottleneckType::Computation
        } else if name_lower.contains("lock") || name_lower.contains("wait") {
            BottleneckType::Lock
        } else {
            BottleneckType::Unknown
        }
    }
}

#[derive(Debug, Clone)]
pub struct Bottleneck {
    pub span_id: SpanId,
    pub span_name: String,
    pub service_name: String,
    pub duration_ms: i64,
    pub percentage: f64,
    pub bottleneck_type: BottleneckType,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BottleneckType {
    Database,
    Network,
    Computation,
    Lock,
    Unknown,
}
```

---

## 📊 服务依赖分析

### 1. 服务拓扑图

```rust
use std::collections::{HashMap, HashSet};

/// 服务拓扑分析器
pub struct ServiceTopologyAnalyzer {
    dependency_graph_builder: Arc<DependencyGraphBuilder>,
}

impl ServiceTopologyAnalyzer {
    pub fn new(dependency_graph_builder: Arc<DependencyGraphBuilder>) -> Self {
        Self { dependency_graph_builder }
    }
    
    /// 构建服务拓扑图
    pub async fn build_topology(
        &self,
        trace_ids: Vec<TraceId>,
    ) -> Result<ServiceTopology, AnalysisError> {
        let mut aggregated_graph = AggregatedDependencyGraph {
            nodes: HashMap::new(),
            edges: HashMap::new(),
        };
        
        // 聚合多个 Trace 的依赖图
        for trace_id in trace_ids {
            if let Ok(graph) = self.dependency_graph_builder
                .build_service_dependency_graph(&trace_id)
                .await
            {
                self.merge_graph(&mut aggregated_graph, graph);
            }
        }
        
        // 计算拓扑统计
        let entry_services = self.find_entry_services(&aggregated_graph);
        let leaf_services = self.find_leaf_services(&aggregated_graph);
        
        Ok(ServiceTopology {
            nodes: aggregated_graph.nodes.into_values().collect(),
            edges: aggregated_graph.edges.into_values().collect(),
            entry_services,
            leaf_services,
        })
    }
    
    /// 合并依赖图
    fn merge_graph(
        &self,
        target: &mut AggregatedDependencyGraph,
        source: ServiceDependencyGraph,
    ) {
        // 合并节点
        for (service_name, node) in source.nodes {
            target
                .nodes
                .entry(service_name.clone())
                .and_modify(|existing| {
                    existing.span_count += node.span_count;
                    existing.total_duration_ms += node.total_duration_ms;
                    existing.trace_count += 1;
                })
                .or_insert(AggregatedServiceNode {
                    service_name: node.service_name,
                    span_count: node.span_count,
                    total_duration_ms: node.total_duration_ms,
                    trace_count: 1,
                });
        }
        
        // 合并边
        for edge in source.edges {
            let edge_key = (edge.from.clone(), edge.to.clone());
            
            target
                .edges
                .entry(edge_key.clone())
                .and_modify(|existing| {
                    existing.call_count += edge.call_count;
                })
                .or_insert(AggregatedDependencyEdge {
                    from: edge.from,
                    to: edge.to,
                    call_count: edge.call_count,
                });
        }
    }
    
    /// 找出入口服务（没有入边的服务）
    fn find_entry_services(&self, graph: &AggregatedDependencyGraph) -> Vec<String> {
        let mut services_with_incoming: HashSet<String> = graph
            .edges
            .values()
            .map(|edge| edge.to.clone())
            .collect();
        
        graph
            .nodes
            .keys()
            .filter(|service| !services_with_incoming.contains(*service))
            .cloned()
            .collect()
    }
    
    /// 找出叶子服务（没有出边的服务）
    fn find_leaf_services(&self, graph: &AggregatedDependencyGraph) -> Vec<String> {
        let services_with_outgoing: HashSet<String> = graph
            .edges
            .values()
            .map(|edge| edge.from.clone())
            .collect();
        
        graph
            .nodes
            .keys()
            .filter(|service| !services_with_outgoing.contains(*service))
            .cloned()
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct AggregatedDependencyGraph {
    pub nodes: HashMap<String, AggregatedServiceNode>,
    pub edges: HashMap<(String, String), AggregatedDependencyEdge>,
}

#[derive(Debug, Clone)]
pub struct AggregatedServiceNode {
    pub service_name: String,
    pub span_count: usize,
    pub total_duration_ms: i64,
    pub trace_count: usize,
}

#[derive(Debug, Clone)]
pub struct AggregatedDependencyEdge {
    pub from: String,
    pub to: String,
    pub call_count: usize,
}

#[derive(Debug, Clone)]
pub struct ServiceTopology {
    pub nodes: Vec<AggregatedServiceNode>,
    pub edges: Vec<AggregatedDependencyEdge>,
    pub entry_services: Vec<String>,
    pub leaf_services: Vec<String>,
}
```

---

### 2. 依赖深度分析

```rust
/// 依赖深度分析器
pub struct DependencyDepthAnalyzer {
    topology_analyzer: Arc<ServiceTopologyAnalyzer>,
}

impl DependencyDepthAnalyzer {
    pub fn new(topology_analyzer: Arc<ServiceTopologyAnalyzer>) -> Self {
        Self { topology_analyzer }
    }
    
    /// 计算服务依赖深度
    pub fn calculate_dependency_depth(
        &self,
        topology: &ServiceTopology,
    ) -> HashMap<String, usize> {
        let mut depths = HashMap::new();
        
        // 构建邻接表
        let mut adjacency: HashMap<String, Vec<String>> = HashMap::new();
        
        for edge in &topology.edges {
            adjacency
                .entry(edge.from.clone())
                .or_insert_with(Vec::new)
                .push(edge.to.clone());
        }
        
        // 从入口服务开始 BFS
        for entry_service in &topology.entry_services {
            let mut queue = VecDeque::new();
            queue.push_back((entry_service.clone(), 0));
            
            while let Some((service, depth)) = queue.pop_front() {
                // 更新深度（取最大值）
                depths
                    .entry(service.clone())
                    .and_modify(|d| *d = (*d).max(depth))
                    .or_insert(depth);
                
                // 将子服务加入队列
                if let Some(children) = adjacency.get(&service) {
                    for child in children {
                        queue.push_back((child.clone(), depth + 1));
                    }
                }
            }
        }
        
        depths
    }
    
    /// 查找最长依赖链
    pub fn find_longest_dependency_chain(
        &self,
        topology: &ServiceTopology,
    ) -> Vec<String> {
        let depths = self.calculate_dependency_depth(topology);
        
        // 找出最大深度
        let max_depth = depths.values().max().cloned().unwrap_or(0);
        
        // 回溯找出最长链
        let mut chain = Vec::new();
        
        // 从入口服务开始
        for entry_service in &topology.entry_services {
            if let Some(&depth) = depths.get(entry_service) {
                if depth == max_depth {
                    chain = self.backtrack_chain(entry_service, topology, &depths);
                    break;
                }
            }
        }
        
        chain
    }
    
    /// 回溯构建依赖链
    fn backtrack_chain(
        &self,
        start_service: &str,
        topology: &ServiceTopology,
        depths: &HashMap<String, usize>,
    ) -> Vec<String> {
        let mut chain = vec![start_service.to_string()];
        let mut current_service = start_service.to_string();
        let mut current_depth = *depths.get(start_service).unwrap_or(&0);
        
        loop {
            // 找到下一个深度的子服务
            let next_service = topology
                .edges
                .iter()
                .filter(|edge| edge.from == current_service)
                .find_map(|edge| {
                    let child_depth = *depths.get(&edge.to)?;
                    
                    if child_depth == current_depth + 1 {
                        Some(edge.to.clone())
                    } else {
                        None
                    }
                });
            
            match next_service {
                Some(next) => {
                    chain.push(next.clone());
                    current_service = next;
                    current_depth += 1;
                }
                None => break,
            }
        }
        
        chain
    }
}
```

---

### 3. 循环依赖检测

```rust
/// 循环依赖检测器
pub struct CircularDependencyDetector {
    topology_analyzer: Arc<ServiceTopologyAnalyzer>,
}

impl CircularDependencyDetector {
    pub fn new(topology_analyzer: Arc<ServiceTopologyAnalyzer>) -> Self {
        Self { topology_analyzer }
    }
    
    /// 检测循环依赖
    pub fn detect_circular_dependencies(
        &self,
        topology: &ServiceTopology,
    ) -> Vec<Vec<String>> {
        let mut cycles = Vec::new();
        
        // 构建邻接表
        let mut adjacency: HashMap<String, Vec<String>> = HashMap::new();
        
        for edge in &topology.edges {
            adjacency
                .entry(edge.from.clone())
                .or_insert_with(Vec::new)
                .push(edge.to.clone());
        }
        
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();
        let mut path = Vec::new();
        
        // DFS 检测环
        for service in topology.nodes.iter().map(|n| &n.service_name) {
            if !visited.contains(service) {
                self.dfs_detect_cycle(
                    service,
                    &adjacency,
                    &mut visited,
                    &mut rec_stack,
                    &mut path,
                    &mut cycles,
                );
            }
        }
        
        cycles
    }
    
    /// DFS 检测环
    fn dfs_detect_cycle(
        &self,
        service: &str,
        adjacency: &HashMap<String, Vec<String>>,
        visited: &mut HashSet<String>,
        rec_stack: &mut HashSet<String>,
        path: &mut Vec<String>,
        cycles: &mut Vec<Vec<String>>,
    ) {
        visited.insert(service.to_string());
        rec_stack.insert(service.to_string());
        path.push(service.to_string());
        
        if let Some(children) = adjacency.get(service) {
            for child in children {
                if !visited.contains(child) {
                    self.dfs_detect_cycle(child, adjacency, visited, rec_stack, path, cycles);
                } else if rec_stack.contains(child) {
                    // 发现环
                    let cycle_start = path.iter().position(|s| s == child).unwrap();
                    let cycle = path[cycle_start..].to_vec();
                    cycles.push(cycle);
                }
            }
        }
        
        path.pop();
        rec_stack.remove(service);
    }
}
```

---

## ⚡ 性能分析

### 1. 耗时分布分析

```rust
/// 耗时分布分析器
pub struct DurationDistributionAnalyzer {
    trace_query_engine: Arc<TraceIdQueryEngine>,
}

impl DurationDistributionAnalyzer {
    pub fn new(trace_query_engine: Arc<TraceIdQueryEngine>) -> Self {
        Self { trace_query_engine }
    }
    
    /// 分析耗时分布
    pub async fn analyze_duration_distribution(
        &self,
        trace_ids: Vec<TraceId>,
    ) -> Result<DurationDistribution, AnalysisError> {
        let mut durations = Vec::new();
        
        for trace_id in trace_ids {
            if let Ok(Some(trace)) = self.trace_query_engine.query_trace(&trace_id).await {
                durations.push(trace.duration_ms);
            }
        }
        
        if durations.is_empty() {
            return Err(AnalysisError::AnalysisFailed("No traces found".to_string()));
        }
        
        durations.sort();
        
        let count = durations.len();
        let sum: i64 = durations.iter().sum();
        let avg = sum / count as i64;
        
        let min = *durations.first().unwrap();
        let max = *durations.last().unwrap();
        
        let median = if count % 2 == 0 {
            (durations[count / 2 - 1] + durations[count / 2]) / 2
        } else {
            durations[count / 2]
        };
        
        // 计算标准差
        let variance: f64 = durations
            .iter()
            .map(|d| {
                let diff = *d as f64 - avg as f64;
                diff * diff
            })
            .sum::<f64>()
            / count as f64;
        
        let std_dev = variance.sqrt();
        
        Ok(DurationDistribution {
            count,
            min,
            max,
            avg,
            median,
            std_dev,
            percentiles: self.calculate_percentiles(&durations),
        })
    }
    
    /// 计算百分位数
    fn calculate_percentiles(&self, sorted_durations: &[i64]) -> Percentiles {
        let len = sorted_durations.len();
        
        Percentiles {
            p50: sorted_durations[len / 2],
            p75: sorted_durations[len * 3 / 4],
            p90: sorted_durations[len * 9 / 10],
            p95: sorted_durations[len * 95 / 100],
            p99: sorted_durations[len * 99 / 100],
        }
    }
}

#[derive(Debug, Clone)]
pub struct DurationDistribution {
    pub count: usize,
    pub min: i64,
    pub max: i64,
    pub avg: i64,
    pub median: i64,
    pub std_dev: f64,
    pub percentiles: Percentiles,
}

#[derive(Debug, Clone)]
pub struct Percentiles {
    pub p50: i64,
    pub p75: i64,
    pub p90: i64,
    pub p95: i64,
    pub p99: i64,
}
```

---

### 2. P95/P99 分析

```rust
/// P95/P99 分析器
pub struct PercentileAnalyzer {
    duration_analyzer: Arc<DurationDistributionAnalyzer>,
}

impl PercentileAnalyzer {
    pub fn new(duration_analyzer: Arc<DurationDistributionAnalyzer>) -> Self {
        Self { duration_analyzer }
    }
    
    /// 分析 P95/P99 趋势
    pub async fn analyze_percentile_trends(
        &self,
        trace_ids_by_window: Vec<(DateTime<Utc>, Vec<TraceId>)>,
    ) -> Result<Vec<PercentileTrend>, AnalysisError> {
        let mut trends = Vec::new();
        
        for (timestamp, trace_ids) in trace_ids_by_window {
            let distribution = self.duration_analyzer
                .analyze_duration_distribution(trace_ids)
                .await?;
            
            trends.push(PercentileTrend {
                timestamp,
                p95: distribution.percentiles.p95,
                p99: distribution.percentiles.p99,
                avg: distribution.avg,
            });
        }
        
        Ok(trends)
    }
    
    /// 检测 P99 异常
    pub fn detect_p99_anomalies(
        &self,
        trends: &[PercentileTrend],
        threshold_multiplier: f64, // 例如 2.0 表示超过平均值的 2 倍
    ) -> Vec<PercentileAnomaly> {
        if trends.is_empty() {
            return Vec::new();
        }
        
        // 计算 P99 的平均值
        let avg_p99 = trends
            .iter()
            .map(|t| t.p99)
            .sum::<i64>() as f64
            / trends.len() as f64;
        
        let threshold = avg_p99 * threshold_multiplier;
        
        trends
            .iter()
            .filter(|trend| trend.p99 as f64 > threshold)
            .map(|trend| PercentileAnomaly {
                timestamp: trend.timestamp,
                p99: trend.p99,
                expected_p99: avg_p99 as i64,
                deviation_percentage: ((trend.p99 as f64 - avg_p99) / avg_p99 * 100.0),
            })
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct PercentileTrend {
    pub timestamp: DateTime<Utc>,
    pub p95: i64,
    pub p99: i64,
    pub avg: i64,
}

#[derive(Debug, Clone)]
pub struct PercentileAnomaly {
    pub timestamp: DateTime<Utc>,
    pub p99: i64,
    pub expected_p99: i64,
    pub deviation_percentage: f64,
}
```

---

### 3. 异常检测

```rust
/// 异常检测器
pub struct AnomalyDetector {
    duration_analyzer: Arc<DurationDistributionAnalyzer>,
}

impl AnomalyDetector {
    pub fn new(duration_analyzer: Arc<DurationDistributionAnalyzer>) -> Self {
        Self { duration_analyzer }
    }
    
    /// 检测异常 Trace（基于统计方法）
    pub async fn detect_anomalies(
        &self,
        trace_ids: Vec<TraceId>,
        sigma_threshold: f64, // 例如 3.0 表示 3 倍标准差
    ) -> Result<Vec<AnomalyTrace>, AnalysisError> {
        let distribution = self.duration_analyzer
            .analyze_duration_distribution(trace_ids.clone())
            .await?;
        
        let upper_bound = distribution.avg as f64 + sigma_threshold * distribution.std_dev;
        let lower_bound = (distribution.avg as f64 - sigma_threshold * distribution.std_dev).max(0.0);
        
        let mut anomalies = Vec::new();
        
        for trace_id in trace_ids {
            if let Ok(Some(trace)) = self.duration_analyzer
                .trace_query_engine
                .query_trace(&trace_id)
                .await
            {
                let duration = trace.duration_ms as f64;
                
                if duration > upper_bound || duration < lower_bound {
                    anomalies.push(AnomalyTrace {
                        trace_id,
                        duration_ms: trace.duration_ms,
                        expected_range: (lower_bound as i64, upper_bound as i64),
                        anomaly_type: if duration > upper_bound {
                            AnomalyType::SlowResponse
                        } else {
                            AnomalyType::FastResponse
                        },
                    });
                }
            }
        }
        
        Ok(anomalies)
    }
}

#[derive(Debug, Clone)]
pub struct AnomalyTrace {
    pub trace_id: TraceId,
    pub duration_ms: i64,
    pub expected_range: (i64, i64),
    pub anomaly_type: AnomalyType,
}

#[derive(Debug, Clone)]
pub enum AnomalyType {
    SlowResponse,
    FastResponse,
}
```

---

## 🎨 Trace 可视化

### 1. 瀑布图生成

```rust
/// 瀑布图生成器
pub struct WaterfallChartGenerator {
    trace_reconstructor: Arc<TraceReconstructor>,
}

impl WaterfallChartGenerator {
    pub fn new(trace_reconstructor: Arc<TraceReconstructor>) -> Self {
        Self { trace_reconstructor }
    }
    
    /// 生成瀑布图数据
    pub async fn generate_waterfall(
        &self,
        trace_id: &TraceId,
    ) -> Result<WaterfallChart, AnalysisError> {
        let trace_tree = self.trace_reconstructor
            .reconstruct_trace_tree(trace_id)
            .await?;
        
        let mut bars = Vec::new();
        
        // 找到最早的开始时间作为基准
        let base_time = trace_tree
            .root_nodes
            .first()
            .map(|root| root.span.start_time)
            .ok_or(AnalysisError::AnalysisFailed("No root nodes".to_string()))?;
        
        // 遍历树生成瀑布图条目
        for root in &trace_tree.root_nodes {
            self.traverse_for_waterfall(root, &mut bars, base_time, 0);
        }
        
        Ok(WaterfallChart {
            trace_id: *trace_id,
            base_time,
            bars,
        })
    }
    
    /// 递归遍历生成瀑布图条目
    fn traverse_for_waterfall(
        &self,
        node: &TraceTreeNode,
        bars: &mut Vec<WaterfallBar>,
        base_time: DateTime<Utc>,
        depth: usize,
    ) {
        let start_offset = (node.span.start_time - base_time).num_milliseconds();
        
        bars.push(WaterfallBar {
            span_id: node.span.span_id,
            span_name: node.span.name.clone(),
            service_name: node.span.service_name.clone(),
            start_offset_ms: start_offset,
            duration_ms: node.span.duration_ms,
            depth,
        });
        
        for child in &node.children {
            self.traverse_for_waterfall(child, bars, base_time, depth + 1);
        }
    }
}

#[derive(Debug, Clone)]
pub struct WaterfallChart {
    pub trace_id: TraceId,
    pub base_time: DateTime<Utc>,
    pub bars: Vec<WaterfallBar>,
}

#[derive(Debug, Clone)]
pub struct WaterfallBar {
    pub span_id: SpanId,
    pub span_name: String,
    pub service_name: String,
    pub start_offset_ms: i64,
    pub duration_ms: i64,
    pub depth: usize,
}
```

---

### 2. 火焰图生成

```rust
/// 火焰图生成器
pub struct FlameGraphGenerator {
    trace_reconstructor: Arc<TraceReconstructor>,
}

impl FlameGraphGenerator {
    pub fn new(trace_reconstructor: Arc<TraceReconstructor>) -> Self {
        Self { trace_reconstructor }
    }
    
    /// 生成火焰图数据
    pub async fn generate_flame_graph(
        &self,
        trace_id: &TraceId,
    ) -> Result<FlameGraph, AnalysisError> {
        let trace_tree = self.trace_reconstructor
            .reconstruct_trace_tree(trace_id)
            .await?;
        
        let mut flame_nodes = Vec::new();
        
        for root in &trace_tree.root_nodes {
            let node = self.build_flame_node(root);
            flame_nodes.push(node);
        }
        
        Ok(FlameGraph {
            trace_id: *trace_id,
            roots: flame_nodes,
        })
    }
    
    /// 递归构建火焰图节点
    fn build_flame_node(&self, tree_node: &TraceTreeNode) -> FlameNode {
        let children: Vec<FlameNode> = tree_node
            .children
            .iter()
            .map(|child| self.build_flame_node(child))
            .collect();
        
        FlameNode {
            name: format!("{} ({})", tree_node.span.service_name, tree_node.span.name),
            value: tree_node.span.duration_ms,
            children,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FlameGraph {
    pub trace_id: TraceId,
    pub roots: Vec<FlameNode>,
}

#[derive(Debug, Clone)]
pub struct FlameNode {
    pub name: String,
    pub value: i64,
    pub children: Vec<FlameNode>,
}
```

---

### 3. Gantt 图生成

```rust
/// Gantt 图生成器
pub struct GanttChartGenerator {
    waterfall_generator: Arc<WaterfallChartGenerator>,
}

impl GanttChartGenerator {
    pub fn new(waterfall_generator: Arc<WaterfallChartGenerator>) -> Self {
        Self { waterfall_generator }
    }
    
    /// 生成 Gantt 图数据
    pub async fn generate_gantt(
        &self,
        trace_id: &TraceId,
    ) -> Result<GanttChart, AnalysisError> {
        let waterfall = self.waterfall_generator
            .generate_waterfall(trace_id)
            .await?;
        
        // 按服务分组
        let mut service_groups: HashMap<String, Vec<GanttTask>> = HashMap::new();
        
        for bar in waterfall.bars {
            let task = GanttTask {
                task_id: format!("{:?}", bar.span_id),
                task_name: bar.span_name,
                start_offset_ms: bar.start_offset_ms,
                duration_ms: bar.duration_ms,
            };
            
            service_groups
                .entry(bar.service_name)
                .or_insert_with(Vec::new)
                .push(task);
        }
        
        Ok(GanttChart {
            trace_id: *trace_id,
            base_time: waterfall.base_time,
            service_groups,
        })
    }
}

#[derive(Debug, Clone)]
pub struct GanttChart {
    pub trace_id: TraceId,
    pub base_time: DateTime<Utc>,
    pub service_groups: HashMap<String, Vec<GanttTask>>,
}

#[derive(Debug, Clone)]
pub struct GanttTask {
    pub task_id: String,
    pub task_name: String,
    pub start_offset_ms: i64,
    pub duration_ms: i64,
}
```

---

## 📈 聚合分析

### 1. 时间窗口聚合

```rust
/// 时间窗口聚合器
pub struct TimeWindowAggregator {
    trace_query_engine: Arc<TraceIdQueryEngine>,
}

impl TimeWindowAggregator {
    pub fn new(trace_query_engine: Arc<TraceIdQueryEngine>) -> Self {
        Self { trace_query_engine }
    }
    
    /// 按时间窗口聚合
    pub async fn aggregate_by_time_window(
        &self,
        trace_ids: Vec<TraceId>,
        window_size_minutes: i64,
    ) -> Result<Vec<TimeWindowAggregation>, AnalysisError> {
        let mut trace_by_window: HashMap<i64, Vec<CompleteTrace>> = HashMap::new();
        
        for trace_id in trace_ids {
            if let Ok(Some(trace)) = self.trace_query_engine.query_trace(&trace_id).await {
                let window_key = trace.start_time.timestamp() / (window_size_minutes * 60);
                
                trace_by_window
                    .entry(window_key)
                    .or_insert_with(Vec::new)
                    .push(trace);
            }
        }
        
        let mut aggregations = Vec::new();
        
        for (window_key, traces) in trace_by_window {
            let window_start = DateTime::from_timestamp(window_key * window_size_minutes * 60, 0)
                .unwrap();
            
            let count = traces.len();
            let total_duration: i64 = traces.iter().map(|t| t.duration_ms).sum();
            let avg_duration = total_duration / count as i64;
            
            let error_count = traces
                .iter()
                .filter(|t| {
                    t.spans
                        .iter()
                        .any(|s| matches!(s.status, SpanStatus::Error { .. }))
                })
                .count();
            
            aggregations.push(TimeWindowAggregation {
                window_start,
                window_size_minutes,
                trace_count: count,
                avg_duration_ms: avg_duration,
                error_count,
            });
        }
        
        aggregations.sort_by_key(|a| a.window_start);
        
        Ok(aggregations)
    }
}

#[derive(Debug, Clone)]
pub struct TimeWindowAggregation {
    pub window_start: DateTime<Utc>,
    pub window_size_minutes: i64,
    pub trace_count: usize,
    pub avg_duration_ms: i64,
    pub error_count: usize,
}
```

---

### 2. 服务级别聚合

```rust
/// 服务级别聚合器
pub struct ServiceLevelAggregator {
    trace_query_engine: Arc<TraceIdQueryEngine>,
}

impl ServiceLevelAggregator {
    pub fn new(trace_query_engine: Arc<TraceIdQueryEngine>) -> Self {
        Self { trace_query_engine }
    }
    
    /// 按服务聚合统计
    pub async fn aggregate_by_service(
        &self,
        trace_ids: Vec<TraceId>,
    ) -> Result<Vec<ServiceAggregation>, AnalysisError> {
        let mut service_stats: HashMap<String, ServiceStatsAccumulator> = HashMap::new();
        
        for trace_id in trace_ids {
            if let Ok(Some(trace)) = self.trace_query_engine.query_trace(&trace_id).await {
                for span in &trace.spans {
                    let stats = service_stats
                        .entry(span.service_name.clone())
                        .or_insert_with(|| ServiceStatsAccumulator {
                            service_name: span.service_name.clone(),
                            span_count: 0,
                            total_duration_ms: 0,
                            error_count: 0,
                            durations: Vec::new(),
                        });
                    
                    stats.span_count += 1;
                    stats.total_duration_ms += span.duration_ms;
                    stats.durations.push(span.duration_ms);
                    
                    if matches!(span.status, SpanStatus::Error { .. }) {
                        stats.error_count += 1;
                    }
                }
            }
        }
        
        let aggregations: Vec<ServiceAggregation> = service_stats
            .into_values()
            .map(|mut stats| {
                stats.durations.sort();
                
                let avg_duration = stats.total_duration_ms / stats.span_count as i64;
                let p95_duration = stats.durations[stats.durations.len() * 95 / 100];
                
                ServiceAggregation {
                    service_name: stats.service_name,
                    span_count: stats.span_count,
                    avg_duration_ms: avg_duration,
                    p95_duration_ms: p95_duration,
                    error_count: stats.error_count,
                    error_rate: (stats.error_count as f64 / stats.span_count as f64) * 100.0,
                }
            })
            .collect();
        
        Ok(aggregations)
    }
}

#[derive(Debug)]
struct ServiceStatsAccumulator {
    service_name: String,
    span_count: usize,
    total_duration_ms: i64,
    error_count: usize,
    durations: Vec<i64>,
}

#[derive(Debug, Clone)]
pub struct ServiceAggregation {
    pub service_name: String,
    pub span_count: usize,
    pub avg_duration_ms: i64,
    pub p95_duration_ms: i64,
    pub error_count: usize,
    pub error_rate: f64,
}
```

---

## 🔍 根因分析

### 1. 错误传播分析

```rust
/// 错误传播分析器
pub struct ErrorPropagationAnalyzer {
    trace_reconstructor: Arc<TraceReconstructor>,
}

impl ErrorPropagationAnalyzer {
    pub fn new(trace_reconstructor: Arc<TraceReconstructor>) -> Self {
        Self { trace_reconstructor }
    }
    
    /// 分析错误传播链
    pub async fn analyze_error_propagation(
        &self,
        trace_id: &TraceId,
    ) -> Result<ErrorPropagationChain, AnalysisError> {
        let trace_tree = self.trace_reconstructor
            .reconstruct_trace_tree(trace_id)
            .await?;
        
        let mut error_spans = Vec::new();
        
        // 收集所有错误 Span
        for root in &trace_tree.root_nodes {
            self.collect_error_spans(root, &mut error_spans);
        }
        
        if error_spans.is_empty() {
            return Err(AnalysisError::AnalysisFailed("No errors found".to_string()));
        }
        
        // 找出最早的错误（根因）
        error_spans.sort_by_key(|span| span.start_time);
        
        let root_cause = error_spans.first().unwrap().clone();
        
        Ok(ErrorPropagationChain {
            trace_id: *trace_id,
            root_cause,
            propagated_errors: error_spans,
        })
    }
    
    /// 收集错误 Span
    fn collect_error_spans(&self, node: &TraceTreeNode, errors: &mut Vec<SpanRecord>) {
        if matches!(node.span.status, SpanStatus::Error { .. }) {
            errors.push(node.span.clone());
        }
        
        for child in &node.children {
            self.collect_error_spans(child, errors);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ErrorPropagationChain {
    pub trace_id: TraceId,
    pub root_cause: SpanRecord,
    pub propagated_errors: Vec<SpanRecord>,
}
```

---

### 2. 异常根因定位

```rust
/// 异常根因定位器
pub struct RootCauseLocator {
    error_propagation_analyzer: Arc<ErrorPropagationAnalyzer>,
    bottleneck_detector: Arc<BottleneckDetector>,
}

impl RootCauseLocator {
    pub fn new(
        error_propagation_analyzer: Arc<ErrorPropagationAnalyzer>,
        bottleneck_detector: Arc<BottleneckDetector>,
    ) -> Self {
        Self {
            error_propagation_analyzer,
            bottleneck_detector,
        }
    }
    
    /// 定位异常根因
    pub async fn locate_root_cause(
        &self,
        trace_id: &TraceId,
    ) -> Result<RootCauseAnalysis, AnalysisError> {
        let mut root_causes = Vec::new();
        
        // 1. 检查错误传播
        if let Ok(error_chain) = self.error_propagation_analyzer
            .analyze_error_propagation(trace_id)
            .await
        {
            root_causes.push(RootCause {
                cause_type: RootCauseType::Error,
                span_id: error_chain.root_cause.span_id,
                span_name: error_chain.root_cause.name.clone(),
                service_name: error_chain.root_cause.service_name.clone(),
                description: format!(
                    "Error originated in {} service",
                    error_chain.root_cause.service_name
                ),
            });
        }
        
        // 2. 检查性能瓶颈
        if let Ok(bottlenecks) = self.bottleneck_detector
            .detect_bottlenecks(trace_id, 20.0)
            .await
        {
            for bottleneck in bottlenecks {
                root_causes.push(RootCause {
                    cause_type: RootCauseType::PerformanceBottleneck,
                    span_id: bottleneck.span_id,
                    span_name: bottleneck.span_name.clone(),
                    service_name: bottleneck.service_name.clone(),
                    description: format!(
                        "{:?} bottleneck taking {:.1}% of total time",
                        bottleneck.bottleneck_type,
                        bottleneck.percentage
                    ),
                });
            }
        }
        
        Ok(RootCauseAnalysis {
            trace_id: *trace_id,
            root_causes,
        })
    }
}

#[derive(Debug, Clone)]
pub struct RootCauseAnalysis {
    pub trace_id: TraceId,
    pub root_causes: Vec<RootCause>,
}

#[derive(Debug, Clone)]
pub struct RootCause {
    pub cause_type: RootCauseType,
    pub span_id: SpanId,
    pub span_name: String,
    pub service_name: String,
    pub description: String,
}

#[derive(Debug, Clone)]
pub enum RootCauseType {
    Error,
    PerformanceBottleneck,
    Timeout,
    ResourceExhaustion,
}
```

---

## 📊 完整示例：Trace 分析平台

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();
    
    println!("🎯 Trace 分析平台启动中...\n");
    
    // 初始化核心组件
    let trace_query_engine = Arc::new(TraceIdQueryEngine::new());
    let trace_reconstructor = Arc::new(TraceReconstructor::new(trace_query_engine.clone()));
    
    // 创建分析器
    let call_chain_analyzer = Arc::new(CallChainAnalyzer::new(trace_reconstructor.clone()));
    let critical_path_analyzer = Arc::new(CriticalPathAnalyzer::new(call_chain_analyzer.clone()));
    let bottleneck_detector = Arc::new(BottleneckDetector::new(critical_path_analyzer.clone()));
    
    // 创建可视化生成器
    let waterfall_generator = Arc::new(WaterfallChartGenerator::new(trace_reconstructor.clone()));
    let flame_generator = Arc::new(FlameGraphGenerator::new(trace_reconstructor.clone()));
    
    let trace_id = [1u8; 16];
    
    println!("📊 执行完整的 Trace 分析...\n");
    
    // 1. 调用链路分析
    if let Ok(chain_analysis) = call_chain_analyzer.analyze_call_chain(&trace_id).await {
        println!("🔗 调用链路分析:");
        println!("  最大深度: {}", chain_analysis.max_depth);
        println!("  总调用数: {}", chain_analysis.total_calls);
    }
    
    // 2. 关键路径分析
    if let Ok(critical_path) = critical_path_analyzer.find_critical_path(&trace_id).await {
        println!("\n⚡ 关键路径:");
        println!("  总耗时: {}ms", critical_path.total_duration);
        println!("  关键节点数: {}", critical_path.critical_nodes.len());
        
        let contributions = critical_path_analyzer.calculate_span_contribution(&critical_path);
        
        println!("\n  Span 耗时占比:");
        for contrib in contributions.iter().take(5) {
            println!(
                "    - {} ({}) : {:.1}%",
                contrib.span_name,
                contrib.service_name,
                contrib.percentage
            );
        }
    }
    
    // 3. 瓶颈检测
    if let Ok(bottlenecks) = bottleneck_detector.detect_bottlenecks(&trace_id, 15.0).await {
        println!("\n🔍 性能瓶颈:");
        
        for bottleneck in bottlenecks {
            println!(
                "  - {} ({:?}): {}ms ({:.1}%)",
                bottleneck.span_name,
                bottleneck.bottleneck_type,
                bottleneck.duration_ms,
                bottleneck.percentage
            );
        }
    }
    
    // 4. 生成瀑布图
    if let Ok(waterfall) = waterfall_generator.generate_waterfall(&trace_id).await {
        println!("\n🌊 瀑布图数据:");
        println!("  基准时间: {}", waterfall.base_time);
        println!("  总条目数: {}", waterfall.bars.len());
    }
    
    // 5. 生成火焰图
    if let Ok(flame_graph) = flame_generator.generate_flame_graph(&trace_id).await {
        println!("\n🔥 火焰图数据:");
        println!("  根节点数: {}", flame_graph.roots.len());
    }
    
    println!("\n✅ 分析完成！");
    
    Ok(())
}

// 占位实现
pub struct TraceIdQueryEngine {}
impl TraceIdQueryEngine {
    pub fn new() -> Self { Self {} }
    pub async fn query_trace(&self, _trace_id: &TraceId) -> Result<Option<CompleteTrace>, AnalysisError> {
        Ok(None)
    }
}

pub struct TraceReconstructor {
    _trace_query_engine: Arc<TraceIdQueryEngine>,
}
impl TraceReconstructor {
    pub fn new(_trace_query_engine: Arc<TraceIdQueryEngine>) -> Self {
        Self { _trace_query_engine }
    }
    pub async fn reconstruct_trace_tree(&self, _trace_id: &TraceId) -> Result<TraceTree, AnalysisError> {
        Err(AnalysisError::TraceNotFound)
    }
}

pub struct DependencyGraphBuilder {}
impl DependencyGraphBuilder {
    pub async fn build_service_dependency_graph(&self, _trace_id: &TraceId) -> Result<ServiceDependencyGraph, AnalysisError> {
        Err(AnalysisError::TraceNotFound)
    }
}

#[derive(Debug, Clone)]
pub struct TraceTree {
    pub trace_id: TraceId,
    pub root_nodes: Vec<TraceTreeNode>,
}

#[derive(Debug, Clone)]
pub struct TraceTreeNode {
    pub span: SpanRecord,
    pub children: Vec<TraceTreeNode>,
}

#[derive(Debug, Clone)]
pub struct SpanRecord {
    pub span_id: SpanId,
    pub parent_span_id: Option<SpanId>,
    pub trace_id: TraceId,
    pub name: String,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub duration_ms: i64,
    pub service_name: String,
    pub attributes: HashMap<String, String>,
    pub status: SpanStatus,
}

#[derive(Debug, Clone)]
pub enum SpanStatus {
    Ok,
    Error { message: String },
}

#[derive(Debug, Clone)]
pub struct CompleteTrace {
    pub trace_id: TraceId,
    pub spans: Vec<SpanRecord>,
    pub start_time: DateTime<Utc>,
    pub end_time: DateTime<Utc>,
    pub duration_ms: i64,
    pub service_count: usize,
    pub span_count: usize,
}

#[derive(Debug, Clone)]
pub struct ServiceDependencyGraph {
    pub nodes: HashMap<String, ServiceNode>,
    pub edges: Vec<ServiceDependencyEdge>,
}

#[derive(Debug, Clone)]
pub struct ServiceNode {
    pub service_name: String,
    pub span_count: usize,
    pub total_duration_ms: i64,
}

#[derive(Debug, Clone)]
pub struct ServiceDependencyEdge {
    pub from: String,
    pub to: String,
    pub call_count: usize,
}
```

---

## 🎯 最佳实践

### 性能优化

1. **缓存重建结果** - Trace 树重建结果应缓存
2. **并行分析** - 多个分析任务并行执行
3. **增量计算** - 聚合统计使用增量更新

### 可视化建议

1. **瀑布图** - 适合查看时序关系
2. **火焰图** - 适合识别热点
3. **Gantt 图** - 适合并发分析

### 分析策略

1. **先宏观后微观** - 先看整体再看细节
2. **关注关键路径** - 优先分析关键路径
3. **结合多维度** - 错误、性能、依赖综合分析

---

## 📚 参考资源

- [Jaeger UI](https://www.jaegertracing.io/docs/latest/frontend-ui/)
- [Zipkin UI](https://zipkin.io/pages/instrumenting.html)
- [Grafana Tempo](https://grafana.com/docs/tempo/latest/)

---

**文档版本**: v1.0.0  
**最后更新**: 2025-10-10  
**作者**: OTLP Rust 项目组
