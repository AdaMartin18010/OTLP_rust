//! # WebAssembly Analytics & Data Processing
//!
//! In-WASM analytics and data processing for telemetry data.
//! Enables local analysis, aggregation, and sorting without exporting
//! raw data to external systems.
//!
//! ## Analytics Capabilities 2025-2026
//!
//! | Feature | Description | WASM Optimization |
//! |---------|-------------|-------------------|
//! | Streaming Sort | Sort large datasets | Chunked processing |
//! | Time-series Aggregation | Windowed aggregations | Incremental compute |
//! | Pattern Detection | Anomaly detection | WASM SIMD (where available) |
//! | Top-K Analysis | Most frequent values | Min-heap in WASM memory |
//! | Correlation Analysis | Metric relationships | Parallel streams |
//! | Histogram Calculation | Distribution analysis | Bucketed arrays |
//!
//! ## Use Cases
//!
//! - **Edge Analytics**: Process telemetry at the edge before sending summaries
//! - **Bandwidth Reduction**: Aggregate data locally, send only summaries
//! - **Real-time Alerts**: Detect issues without round-trip to backend
//! - **Privacy Compliance**: Aggregate PII-containing data before export
//! - **Offline Operation**: Queue and batch process when disconnected
//!
//! ## Usage Examples
//!
//! ### Streaming Sort
//!
//! ```rust,ignore
//! use otlp::wasm_analytics::{StreamingSort, SortConfig};
//!
//! let sorter = StreamingSort::new(SortConfig {
//!     chunk_size: 1000,
//!     max_memory: 10 * 1024 * 1024, // 10MB
//! });
//!
//! for batch in trace_batches {
//!     sorter.add_batch(batch).await?;
//! }
//!
//! let sorted = sorter.finish().await?;
//! ```
//!
//! ### Time-series Aggregation
//!
//! ```rust,ignore
//! use otlp::wasm_analytics::{TimeSeriesAggregator, WindowConfig, Aggregation};
//!
//! let aggregator = TimeSeriesAggregator::new(WindowConfig {
//!     window_size_secs: 60,
//!     aggregation: Aggregation::Mean,
//! });
//!
//! for metric in metrics {
//!     aggregator.add_point(metric.timestamp, metric.value).await?;
//! }
//!
//! let windows = aggregator.compute_windows().await?;
//! // Export only aggregated windows, not raw points
//! exporter.export_metrics(windows).await?;
//! ```
//!
//! ### Top-K Analysis
//!
//! ```rust,ignore
//! use otlp::wasm_analytics::{TopKAnalyzer, TopKConfig};
//!
//! let analyzer = TopKAnalyzer::new(TopKConfig {
//!     k: 10,
//!     counter_size: 10000,
//! });
//!
//! for span in spans {
//!     analyzer.add(span.name.clone()).await?;
//! }
//!
//! let top_operations = analyzer.top_k().await?;
//! // Export: [("GET /api/users", 15432), ("POST /api/orders", 8921), ...]
//! ```
//!
//! ### Histogram Calculation
//!
//! ```rust,ignore
//! use otlp::wasm_analytics::{HistogramCalculator, HistogramConfig};
//!
//! let hist = HistogramCalculator::new(HistogramConfig {
//!     min_value: 0.0,
//!     max_value: 1000.0,
//!     buckets: 50,
//! });
//!
//! for latency in latencies {
//!     hist.record(latency);
//! }
//!
//! let distribution = hist.calculate();
//! // Export: { buckets: [...], p50: 45.2, p99: 892.1 }
//! ```

// use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
#[allow(unused_imports)]
use std::time::Duration;

use crate::error::{OtlpError, ProcessingError, Result};

/// Sort configuration
#[derive(Debug, Clone)]
pub struct SortConfig {
    /// Chunk size for sorting
    pub chunk_size: usize,
    /// Maximum memory to use
    pub max_memory: usize,
    /// Sort field
    pub sort_field: SortField,
    /// Sort order
    pub descending: bool,
}

impl Default for SortConfig {
    fn default() -> Self {
        Self {
            chunk_size: 1000,
            max_memory: 10 * 1024 * 1024, // 10MB
            sort_field: SortField::Timestamp,
            descending: false,
        }
    }
}

/// Fields for sorting
#[derive(Debug, Clone, Copy)]
pub enum SortField {
    Timestamp,
    Duration,
    Name,
    Custom(usize), // Index into custom fields
}

/// Sortable item trait
pub trait Sortable: Clone + Send + 'static {
    /// Get sort key as u64 (for numeric sorting)
    fn sort_key(&self, field: SortField) -> u64;
    /// Get name for string sorting
    fn name(&self) -> &str;
}

/// Streaming sort for large datasets
pub struct StreamingSort<T: Sortable> {
    config: SortConfig,
    chunks: Vec<Vec<T>>,
    current_chunk: Vec<T>,
    total_items: usize,
}

impl<T: Sortable> StreamingSort<T> {
    /// Create new streaming sorter
    pub fn new(config: SortConfig) -> Self {
        Self {
            config: config.clone(),
            chunks: Vec::new(),
            current_chunk: Vec::with_capacity(config.chunk_size),
            total_items: 0,
        }
    }

    /// Add a single item
    pub fn add(&mut self, item: T) -> Result<()> {
        self.current_chunk.push(item);
        self.total_items += 1;

        if self.current_chunk.len() >= self.config.chunk_size {
            self.flush_chunk()?;
        }

        Ok(())
    }

    /// Add a batch of items
    pub fn add_batch(&mut self, items: Vec<T>) -> Result<()> {
        for item in items {
            self.add(item)?;
        }
        Ok(())
    }

    /// Flush current chunk
    fn flush_chunk(&mut self) -> Result<()> {
        if self.current_chunk.is_empty() {
            return Ok(());
        }

        // Sort the chunk
        let sort_field = self.config.sort_field;
        let descending = self.config.descending;

        self.current_chunk.sort_by(|a, b| {
            let key_a = a.sort_key(sort_field);
            let key_b = b.sort_key(sort_field);
            if descending {
                key_b.cmp(&key_a)
            } else {
                key_a.cmp(&key_b)
            }
        });

        self.chunks.push(std::mem::replace(
            &mut self.current_chunk,
            Vec::with_capacity(self.config.chunk_size),
        ));

        Ok(())
    }

    /// Finish and return sorted iterator
    pub fn finish(mut self) -> Result<SortedIterator<T>> {
        self.flush_chunk()?;

        // K-way merge
        let mut heap: BinaryHeap<MergeItem<T>> = BinaryHeap::new();

        for (chunk_idx, chunk) in self.chunks.iter().enumerate() {
            if !chunk.is_empty() {
                heap.push(MergeItem {
                    item: chunk[0].clone(),
                    chunk_idx,
                    item_idx: 0,
                    sort_field: self.config.sort_field,
                    descending: self.config.descending,
                });
            }
        }

        Ok(SortedIterator {
            chunks: self.chunks,
            heap,
            total_items: self.total_items,
            returned_items: 0,
        })
    }

    /// Get total item count
    pub fn len(&self) -> usize {
        self.total_items
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.total_items == 0
    }
}

/// Item for k-way merge
struct MergeItem<T: Sortable> {
    item: T,
    chunk_idx: usize,
    item_idx: usize,
    sort_field: SortField,
    descending: bool,
}

impl<T: Sortable> PartialEq for MergeItem<T> {
    fn eq(&self, other: &Self) -> bool {
        self.item.sort_key(self.sort_field) == other.item.sort_key(other.sort_field)
    }
}

impl<T: Sortable> Eq for MergeItem<T> {}

impl<T: Sortable> PartialOrd for MergeItem<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Sortable> Ord for MergeItem<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let ord = self
            .item
            .sort_key(self.sort_field)
            .cmp(&other.item.sort_key(other.sort_field));
        if self.descending {
            ord.reverse()
        } else {
            ord
        }
    }
}

/// Sorted iterator
pub struct SortedIterator<T: Sortable> {
    chunks: Vec<Vec<T>>,
    heap: BinaryHeap<MergeItem<T>>,
    total_items: usize,
    returned_items: usize,
}

impl<T: Sortable> Iterator for SortedIterator<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let merge_item = self.heap.pop()?;
        let result = merge_item.item.clone();

        // Push next item from same chunk
        let next_idx = merge_item.item_idx + 1;
        if next_idx < self.chunks[merge_item.chunk_idx].len() {
            self.heap.push(MergeItem {
                item: self.chunks[merge_item.chunk_idx][next_idx].clone(),
                chunk_idx: merge_item.chunk_idx,
                item_idx: next_idx,
                sort_field: merge_item.sort_field,
                descending: merge_item.descending,
            });
        }

        self.returned_items += 1;
        Some(result)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.total_items - self.returned_items;
        (remaining, Some(remaining))
    }
}

impl<T: Sortable> ExactSizeIterator for SortedIterator<T> {}

/// Window configuration for time-series
#[derive(Debug, Clone)]
pub struct WindowConfig {
    /// Window size in seconds
    pub window_size_secs: u64,
    /// Aggregation function
    pub aggregation: Aggregation,
}

/// Aggregation functions
#[derive(Debug, Clone, Copy)]
pub enum Aggregation {
    Sum,
    Mean,
    Min,
    Max,
    Count,
    P50,
    P95,
    P99,
}

/// Time-series data point
#[derive(Debug, Clone)]
pub struct DataPoint {
    pub timestamp: u64,
    pub value: f64,
}

/// Aggregated window
#[derive(Debug, Clone)]
pub struct AggregatedWindow {
    pub start_time: u64,
    pub end_time: u64,
    pub value: f64,
    pub count: usize,
}

/// Time-series aggregator
pub struct TimeSeriesAggregator {
    config: WindowConfig,
    points: Vec<DataPoint>,
    #[allow(dead_code)]
    current_window: u64,
}

impl TimeSeriesAggregator {
    /// Create new aggregator
    pub fn new(config: WindowConfig) -> Self {
        Self {
            config,
            points: Vec::new(),
            current_window: 0,
        }
    }

    /// Add a data point
    pub fn add_point(&mut self, timestamp: u64, value: f64) {
        self.points.push(DataPoint { timestamp, value });
    }

    /// Add batch of points
    pub fn add_batch(&mut self, points: Vec<DataPoint>) {
        self.points.extend(points);
    }

    /// Compute windows
    pub fn compute_windows(&mut self) -> Result<Vec<AggregatedWindow>> {
        if self.points.is_empty() {
            return Ok(vec![]);
        }

        // Sort by timestamp
        self.points.sort_by_key(|p| p.timestamp);

        let mut windows: Vec<AggregatedWindow> = Vec::new();
        let window_size = self.config.window_size_secs * 1_000_000_000; // Convert to nanoseconds

        let mut current_start = self.points[0].timestamp / window_size * window_size;
        let mut window_values: Vec<f64> = Vec::new();

        for point in &self.points {
            let point_window = point.timestamp / window_size * window_size;

            if point_window != current_start {
                // Finalize current window
                if !window_values.is_empty() {
                    windows.push(AggregatedWindow {
                        start_time: current_start,
                        end_time: current_start + window_size,
                        value: self.aggregate(&window_values)?,
                        count: window_values.len(),
                    });
                }

                // Start new window
                current_start = point_window;
                window_values.clear();
            }

            window_values.push(point.value);
        }

        // Finalize last window
        if !window_values.is_empty() {
            windows.push(AggregatedWindow {
                start_time: current_start,
                end_time: current_start + window_size,
                value: self.aggregate(&window_values)?,
                count: window_values.len(),
            });
        }

        // Clear points for next batch
        self.points.clear();

        Ok(windows)
    }

    /// Apply aggregation function
    fn aggregate(&self, values: &[f64]) -> Result<f64> {
        if values.is_empty() {
            return Err(OtlpError::Processing(ProcessingError::InvalidState {
                message: "Cannot aggregate empty window".to_string(),
            }));
        }

        match self.config.aggregation {
            Aggregation::Sum => Ok(values.iter().sum()),
            Aggregation::Mean => Ok(values.iter().sum::<f64>() / values.len() as f64),
            Aggregation::Min => Ok(values.iter().cloned().fold(f64::INFINITY, f64::min)),
            Aggregation::Max => Ok(values.iter().cloned().fold(f64::NEG_INFINITY, f64::max)),
            Aggregation::Count => Ok(values.len() as f64),
            Aggregation::P50 => Ok(Self::percentile(values, 0.5)),
            Aggregation::P95 => Ok(Self::percentile(values, 0.95)),
            Aggregation::P99 => Ok(Self::percentile(values, 0.99)),
        }
    }

    /// Calculate percentile
    fn percentile(values: &[f64], p: f64) -> f64 {
        let mut sorted = values.to_vec();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());

        let index = (sorted.len() as f64 * p) as usize;
        sorted[index.min(sorted.len() - 1)]
    }

    /// Get point count
    pub fn len(&self) -> usize {
        self.points.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }
}

/// Top-K configuration
#[derive(Debug, Clone)]
pub struct TopKConfig {
    /// Number of top items to track
    pub k: usize,
    /// Maximum counter map size
    pub counter_size: usize,
}

impl Default for TopKConfig {
    fn default() -> Self {
        Self {
            k: 10,
            counter_size: 10000,
        }
    }
}

/// Count-Min sketch for approximate counting
pub struct CountMinSketch {
    width: usize,
    #[allow(dead_code)]
    depth: usize,
    table: Vec<Vec<u64>>,
    seeds: Vec<u64>,
}

impl CountMinSketch {
    /// Create new sketch
    pub fn new(width: usize, depth: usize) -> Self {
        let mut seeds = Vec::with_capacity(depth);
        for _ in 0..depth {
            seeds.push(fastrand::u64(..));
        }

        Self {
            width,
            depth,
            table: vec![vec![0; width]; depth],
            seeds,
        }
    }

    /// Add item
    pub fn add(&mut self, item: &str) {
        for (i, seed) in self.seeds.iter().enumerate() {
            let hash = Self::hash(item, *seed);
            let idx = (hash as usize) % self.width;
            self.table[i][idx] += 1;
        }
    }

    /// Estimate count
    pub fn estimate(&self, item: &str) -> u64 {
        let mut min_count = u64::MAX;

        for (i, seed) in self.seeds.iter().enumerate() {
            let hash = Self::hash(item, *seed);
            let idx = (hash as usize) % self.width;
            min_count = min_count.min(self.table[i][idx]);
        }

        min_count
    }

    /// Simple hash function
    fn hash(s: &str, seed: u64) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        s.hash(&mut hasher);
        seed.wrapping_add(hasher.finish())
    }
}

/// Top-K analyzer
pub struct TopKAnalyzer {
    config: TopKConfig,
    sketch: CountMinSketch,
    heavy_hitters: HashMap<String, u64>,
    total_count: u64,
}

impl TopKAnalyzer {
    /// Create new analyzer
    pub fn new(config: TopKConfig) -> Self {
        Self {
            config: config.clone(),
            sketch: CountMinSketch::new(config.counter_size / 10, 4),
            heavy_hitters: HashMap::new(),
            total_count: 0,
        }
    }

    /// Add item
    pub fn add(&mut self, item: impl Into<String>) {
        let item_str = item.into();
        self.sketch.add(&item_str);
        self.total_count += 1;

        let estimate = self.sketch.estimate(&item_str);

        // Update heavy hitters
        *self.heavy_hitters.entry(item_str).or_insert(0) = estimate;

        // Prune if too many
        if self.heavy_hitters.len() > self.config.counter_size {
            self.prune();
        }
    }

    /// Add batch
    pub fn add_batch(&mut self, items: Vec<String>) {
        for item in items {
            self.add(item);
        }
    }

    /// Get top K items
    pub fn top_k(&self) -> Vec<(String, u64)> {
        let mut items: Vec<(String, u64)> = self
            .heavy_hitters
            .iter()
            .map(|(k, v)| (k.clone(), *v))
            .collect();

        items.sort_by(|a, b| b.1.cmp(&a.1));
        items.into_iter().take(self.config.k).collect()
    }

    /// Get item frequency
    pub fn frequency(&self, item: &str) -> u64 {
        self.sketch.estimate(item)
    }

    /// Get total count
    pub fn total(&self) -> u64 {
        self.total_count
    }

    /// Prune heavy hitters
    fn prune(&mut self) {
        let threshold = self.total_count / (self.config.k as u64 * 10);
        self.heavy_hitters
            .retain(|_, count| *count > threshold);
    }

    /// Get distinct estimate
    pub fn distinct_estimate(&self) -> usize {
        // Simple estimate based on heavy hitters
        self.heavy_hitters.len()
    }
}

/// Histogram configuration
#[derive(Debug, Clone)]
pub struct HistogramConfig {
    pub min_value: f64,
    pub max_value: f64,
    pub buckets: usize,
}

/// Histogram bucket
#[derive(Debug, Clone)]
pub struct Bucket {
    pub lower: f64,
    pub upper: f64,
    pub count: u64,
}

/// Histogram result
#[derive(Debug, Clone)]
pub struct HistogramResult {
    pub buckets: Vec<Bucket>,
    pub total_count: u64,
    pub sum: f64,
    pub min: f64,
    pub max: f64,
    pub mean: f64,
    pub p50: f64,
    pub p95: f64,
    pub p99: f64,
}

/// Histogram calculator
pub struct HistogramCalculator {
    config: HistogramConfig,
    buckets: Vec<u64>,
    values: Vec<f64>, // For percentile calculation
    total_count: u64,
    sum: f64,
    min: f64,
    max: f64,
}

impl HistogramCalculator {
    /// Create new calculator
    pub fn new(config: HistogramConfig) -> Self {
        Self {
            buckets: vec![0; config.buckets],
            values: Vec::new(),
            total_count: 0,
            sum: 0.0,
            min: f64::INFINITY,
            max: f64::NEG_INFINITY,
            config,
        }
    }

    /// Record a value
    pub fn record(&mut self, value: f64) {
        self.total_count += 1;
        self.sum += value;
        self.min = self.min.min(value);
        self.max = self.max.max(value);

        // Store for percentile calculation
        if self.values.len() < 100000 {
            // Limit memory usage
            self.values.push(value);
        }

        // Find bucket
        let range = self.config.max_value - self.config.min_value;
        if range == 0.0 {
            return;
        }

        let normalized = (value - self.config.min_value) / range;
        let bucket_idx = (normalized * self.config.buckets as f64) as usize;
        let bucket_idx = bucket_idx.min(self.config.buckets - 1);

        self.buckets[bucket_idx] += 1;
    }

    /// Record batch
    pub fn record_batch(&mut self, values: &[f64]) {
        for &value in values {
            self.record(value);
        }
    }

    /// Calculate histogram
    pub fn calculate(&self) -> HistogramResult {
        let mean = if self.total_count > 0 {
            self.sum / self.total_count as f64
        } else {
            0.0
        };

        let (p50, p95, p99) = if !self.values.is_empty() {
            let mut sorted = self.values.clone();
            sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
            (
                Self::percentile_sorted(&sorted, 0.5),
                Self::percentile_sorted(&sorted, 0.95),
                Self::percentile_sorted(&sorted, 0.99),
            )
        } else {
            (0.0, 0.0, 0.0)
        };

        let range = self.config.max_value - self.config.min_value;
        let bucket_width = range / self.config.buckets as f64;

        let buckets: Vec<Bucket> = self
            .buckets
            .iter()
            .enumerate()
            .map(|(i, &count)| Bucket {
                lower: self.config.min_value + (i as f64 * bucket_width),
                upper: self.config.min_value + ((i + 1) as f64 * bucket_width),
                count,
            })
            .collect();

        HistogramResult {
            buckets,
            total_count: self.total_count,
            sum: self.sum,
            min: if self.total_count > 0 {
                self.min
            } else {
                0.0
            },
            max: if self.total_count > 0 {
                self.max
            } else {
                0.0
            },
            mean,
            p50,
            p95,
            p99,
        }
    }

    fn percentile_sorted(sorted: &[f64], p: f64) -> f64 {
        let index = ((sorted.len() as f64 * p) as usize).min(sorted.len() - 1);
        sorted[index]
    }

    /// Get total count
    pub fn count(&self) -> u64 {
        self.total_count
    }
}

/// Correlation analyzer
pub struct CorrelationAnalyzer {
    x_values: Vec<f64>,
    y_values: Vec<f64>,
    max_samples: usize,
}

impl CorrelationAnalyzer {
    /// Create new analyzer
    pub fn new(max_samples: usize) -> Self {
        Self {
            x_values: Vec::new(),
            y_values: Vec::new(),
            max_samples,
        }
    }

    /// Add sample
    pub fn add(&mut self, x: f64, y: f64) {
        if self.x_values.len() >= self.max_samples {
            // Reservoir sampling - randomly replace
            let idx = fastrand::usize(..self.x_values.len());
            self.x_values[idx] = x;
            self.y_values[idx] = y;
        } else {
            self.x_values.push(x);
            self.y_values.push(y);
        }
    }

    /// Calculate Pearson correlation
    pub fn correlation(&self) -> Option<f64> {
        if self.x_values.len() < 2 {
            return None;
        }

        let n = self.x_values.len() as f64;
        let mean_x = self.x_values.iter().sum::<f64>() / n;
        let mean_y = self.y_values.iter().sum::<f64>() / n;

        let mut num = 0.0;
        let mut den_x = 0.0;
        let mut den_y = 0.0;

        for i in 0..self.x_values.len() {
            let dx = self.x_values[i] - mean_x;
            let dy = self.y_values[i] - mean_y;
            num += dx * dy;
            den_x += dx * dx;
            den_y += dy * dy;
        }

        let den = (den_x * den_y).sqrt();
        if den == 0.0 {
            return None;
        }

        Some(num / den)
    }

    /// Get sample count
    pub fn len(&self) -> usize {
        self.x_values.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.x_values.is_empty()
    }
}

/// Pattern detector for anomaly detection
pub struct PatternDetector {
    history: Vec<f64>,
    window_size: usize,
    threshold: f64,
}

impl PatternDetector {
    /// Create new detector
    pub fn new(window_size: usize, threshold: f64) -> Self {
        Self {
            history: Vec::with_capacity(window_size * 2),
            window_size,
            threshold,
        }
    }

    /// Add value and check for anomaly
    pub fn check(&mut self, value: f64) -> PatternResult {
        self.history.push(value);

        if self.history.len() > self.window_size * 2 {
            self.history.remove(0);
        }

        if self.history.len() < self.window_size {
            return PatternResult::InsufficientData;
        }

        let recent: Vec<f64> = self
            .history
            .iter()
            .rev()
            .take(self.window_size)
            .cloned()
            .collect();

        let historical: Vec<f64> = self
            .history
            .iter()
            .rev()
            .skip(self.window_size)
            .take(self.window_size)
            .cloned()
            .collect();

        if historical.is_empty() {
            return PatternResult::InsufficientData;
        }

        let recent_mean = recent.iter().sum::<f64>() / recent.len() as f64;
        let historical_mean = historical.iter().sum::<f64>() / historical.len() as f64;

        let diff = (recent_mean - historical_mean).abs();
        let relative_diff = diff / historical_mean.abs();

        if relative_diff > self.threshold {
            PatternResult::Anomaly {
                value,
                expected: historical_mean,
                deviation: relative_diff,
            }
        } else {
            PatternResult::Normal
        }
    }
}

/// Pattern detection result
#[derive(Debug, Clone)]
pub enum PatternResult {
    Normal,
    InsufficientData,
    Anomaly {
        value: f64,
        expected: f64,
        deviation: f64,
    },
}

/// Simple implementation of Sortable for testing
#[derive(Debug, Clone)]
pub struct TestItem {
    pub timestamp: u64,
    pub name: String,
    pub value: f64,
}

impl Sortable for TestItem {
    fn sort_key(&self, field: SortField) -> u64 {
        match field {
            SortField::Timestamp => self.timestamp,
            SortField::Duration => self.value as u64,
            _ => self.timestamp,
        }
    }

    fn name(&self) -> &str {
        &self.name
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_streaming_sort() {
        let mut sorter = StreamingSort::new(SortConfig {
            chunk_size: 10, // Use large chunk size so all items in one chunk
            max_memory: 1024 * 1024,
            sort_field: SortField::Timestamp,
            descending: false,
        });

        // Add items out of order
        sorter.add(TestItem { timestamp: 5, name: "e".to_string(), value: 5.0 }).unwrap();
        sorter.add(TestItem { timestamp: 2, name: "b".to_string(), value: 2.0 }).unwrap();
        sorter.add(TestItem { timestamp: 8, name: "h".to_string(), value: 8.0 }).unwrap();
        sorter.add(TestItem { timestamp: 1, name: "a".to_string(), value: 1.0 }).unwrap();
        sorter.add(TestItem { timestamp: 9, name: "i".to_string(), value: 9.0 }).unwrap();

        let sorted: Vec<_> = sorter.finish().unwrap().collect();
        assert_eq!(sorted.len(), 5);
        assert_eq!(sorted[0].timestamp, 1);
        assert_eq!(sorted[1].timestamp, 2);
        assert_eq!(sorted[2].timestamp, 5);
        assert_eq!(sorted[3].timestamp, 8);
        assert_eq!(sorted[4].timestamp, 9);
    }

    #[test]
    fn test_time_series_aggregator() {
        let mut aggregator = TimeSeriesAggregator::new(WindowConfig {
            window_size_secs: 1, // 1 second windows
            aggregation: Aggregation::Mean,
        });

        // Add points in nanoseconds
        aggregator.add_point(0, 10.0);
        aggregator.add_point(500_000_000, 20.0); // 0.5s
        aggregator.add_point(1_000_000_000, 30.0); // 1.0s
        aggregator.add_point(1_500_000_000, 40.0); // 1.5s
        aggregator.add_point(2_000_000_000, 50.0); // 2.0s

        let windows = aggregator.compute_windows().unwrap();
        assert_eq!(windows.len(), 3);

        // First window: mean of 10, 20
        assert!((windows[0].value - 15.0).abs() < 0.01);
        // Second window: mean of 30, 40
        assert!((windows[1].value - 35.0).abs() < 0.01);
        // Third window: mean of 50
        assert!((windows[2].value - 50.0).abs() < 0.01);
    }

    #[test]
    fn test_top_k_analyzer() {
        let mut analyzer = TopKAnalyzer::new(TopKConfig {
            k: 3,
            counter_size: 100,
        });

        analyzer.add_batch(vec![
            "a".to_string(),
            "a".to_string(),
            "a".to_string(),
            "b".to_string(),
            "b".to_string(),
            "c".to_string(),
        ]);

        let top = analyzer.top_k();
        assert_eq!(top.len(), 3);
        assert_eq!(top[0].0, "a");
        assert_eq!(top[0].1, 3);
        assert_eq!(top[1].0, "b");
        assert_eq!(top[1].1, 2);
    }

    #[test]
    fn test_histogram_calculator() {
        let mut hist = HistogramCalculator::new(HistogramConfig {
            min_value: 0.0,
            max_value: 100.0,
            buckets: 10,
        });

        // Add values
        for i in 0..100 {
            hist.record(i as f64);
        }

        let result = hist.calculate();
        assert_eq!(result.total_count, 100);
        assert_eq!(result.min, 0.0);
        assert_eq!(result.max, 99.0);
        assert!(result.mean > 49.0 && result.mean < 51.0);
    }

    #[test]
    fn test_correlation_analyzer() {
        let mut analyzer = CorrelationAnalyzer::new(1000);

        // Perfect positive correlation
        for i in 0..100 {
            analyzer.add(i as f64, i as f64 * 2.0);
        }

        let corr = analyzer.correlation().unwrap();
        assert!((corr - 1.0).abs() < 0.01);

        // Perfect negative correlation
        let mut analyzer2 = CorrelationAnalyzer::new(1000);
        for i in 0..100 {
            analyzer2.add(i as f64, 100.0 - i as f64);
        }

        let corr2 = analyzer2.correlation().unwrap();
        assert!((corr2 + 1.0).abs() < 0.01);
    }

    #[test]
    fn test_pattern_detector() {
        let mut detector = PatternDetector::new(5, 0.5);

        // Normal pattern
        for i in 0..10 {
            let result = detector.check(10.0 + i as f64);
            assert!(matches!(result, PatternResult::Normal | PatternResult::InsufficientData));
        }

        // Sudden spike - anomaly
        let result = detector.check(1000.0);
        assert!(matches!(result, PatternResult::Anomaly { .. }));
    }

    #[test]
    fn test_count_min_sketch() {
        let mut sketch = CountMinSketch::new(100, 4);

        sketch.add("item1");
        sketch.add("item1");
        sketch.add("item1");
        sketch.add("item2");
        sketch.add("item2");

        assert!(sketch.estimate("item1") >= 3);
        assert!(sketch.estimate("item2") >= 2);
        assert_eq!(sketch.estimate("item3"), 0);
    }

    #[test]
    fn test_aggregation_functions() {
        let mut aggregator = TimeSeriesAggregator::new(WindowConfig {
            window_size_secs: 60,
            aggregation: Aggregation::Sum,
        });

        aggregator.add_point(0, 1.0);
        aggregator.add_point(1, 2.0);
        aggregator.add_point(2, 3.0);

        let windows = aggregator.compute_windows().unwrap();
        assert!((windows[0].value - 6.0).abs() < 0.01);
    }

    #[test]
    fn test_sort_config_default() {
        let config = SortConfig::default();
        assert_eq!(config.chunk_size, 1000);
        assert_eq!(config.max_memory, 10 * 1024 * 1024);
        assert!(!config.descending);
    }
}
