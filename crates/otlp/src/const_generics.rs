//! # Rust 1.94 Const Generics 与 GATs 特性
//!
//! 本模块展示 Rust 1.94 中 const generics 和 Generic Associated Types (GATs) 的高级用法，
//! 这些是 Rust 类型系统的强大特性，用于构建高性能、类型安全的遥测数据处理系统。
//!
//! ## 主要特性
//!
//! - **Const Generics**: 使用编译时常量参数化类型
//! - **GATs (Generic Associated Types)**: 在 trait 中定义泛型关联类型
//! - **const fn 泛型**: 编译时计算的泛型函数
//! - **类型级编程**: 利用类型系统进行编译时优化
//!
//! ## Rust 版本要求
//!
//! - Rust 1.94.0+ (Edition 2024)
//! - const generics 在 Rust 1.51 稳定
//! - GATs 在 Rust 1.65 稳定
//! - const fn 泛型 trait bounds 在 Rust 1.61 稳定
//!
//! ## 性能优势
//!
//! - **零运行时开销**: 编译时常量直接在代码中展开
//! - **类型安全**: 编译时捕获大小不匹配错误
//! - **SIMD 友好**: 固定大小数组利于向量化
//! - **缓存友好**: 编译时已知大小优化内存布局

use std::marker::PhantomData;

/// 编译时固定大小的环形缓冲区
///
/// 使用 const generics 参数化容量，编译时确定大小
///
/// # Type Parameters
/// - `T`: 元素类型
/// - `N`: 编译时确定的缓冲区容量
///
/// # Examples
/// ```
/// use otlp::const_generics::RingBuffer;
///
/// let mut buffer: RingBuffer<i32, 1024> = RingBuffer::new();
/// buffer.push(42);
/// assert_eq!(buffer.get(0), Some(&42));
/// ```
#[derive(Debug, Clone)]
pub struct RingBuffer<T, const N: usize> {
    buffer: [Option<T>; N],
    head: usize,
    tail: usize,
    count: usize,
}

impl<T: Clone, const N: usize> RingBuffer<T, N> {
    /// 创建新的固定大小环形缓冲区
    ///
    /// 使用 `None` 初始化所有槽位
    pub fn new() -> Self {
        // const generics 允许在编译时创建固定大小的数组
        Self {
            buffer: std::array::from_fn(|_| None),
            head: 0,
            tail: 0,
            count: 0,
        }
    }

    /// 添加元素到缓冲区
    pub fn push(&mut self, item: T) {
        self.buffer[self.head] = Some(item);
        self.head = (self.head + 1) % N;
        
        if self.count < N {
            self.count += 1;
        } else {
            // 缓冲区已满，移动 tail
            self.tail = (self.tail + 1) % N;
        }
    }

    /// 从缓冲区弹出元素
    pub fn pop(&mut self) -> Option<T> {
        if self.count == 0 {
            return None;
        }
        
        let item = self.buffer[self.tail].take();
        self.tail = (self.tail + 1) % N;
        self.count -= 1;
        item
    }

    /// 获取索引位置的元素
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.count {
            return None;
        }
        let idx = (self.tail + index) % N;
        self.buffer[idx].as_ref()
    }

    /// 返回当前元素数量
    pub fn len(&self) -> usize {
        self.count
    }

    /// 检查缓冲区是否为空
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// 检查缓冲区是否已满
    pub fn is_full(&self) -> bool {
        self.count == N
    }

    /// 返回缓冲区容量（编译时常量）
    pub const fn capacity() -> usize {
        N
    }

    /// 清空缓冲区
    pub fn clear(&mut self) {
        self.buffer = std::array::from_fn(|_| None);
        self.head = 0;
        self.tail = 0;
        self.count = 0;
    }

    /// 返回迭代器
    pub fn iter(&self) -> impl Iterator<Item = &T> + '_ {
        (0..self.count).filter_map(move |i| self.get(i))
    }
}

impl<T: Clone, const N: usize> Default for RingBuffer<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

/// 编译时类型化的遥测批量处理器
///
/// 使用 const generics 优化批量处理性能
///
/// # Type Parameters
/// - `T`: 遥测数据类型
/// - `BATCH_SIZE`: 编译时确定的批量大小
/// - `TIMEOUT_MS`: 编译时确定的超时时间（毫秒）
#[derive(Debug)]
pub struct TypedBatchProcessor<T, const BATCH_SIZE: usize, const TIMEOUT_MS: u64> {
    items: Vec<T>,
    last_flush: std::time::Instant,
    _phantom: PhantomData<[T; BATCH_SIZE]>,
}

impl<T, const BATCH_SIZE: usize, const TIMEOUT_MS: u64> TypedBatchProcessor<T, BATCH_SIZE, TIMEOUT_MS> {
    /// 创建新的类型化批量处理器
    pub fn new() -> Self {
        Self {
            items: Vec::with_capacity(BATCH_SIZE),
            last_flush: std::time::Instant::now(),
            _phantom: PhantomData,
        }
    }

    /// 添加项目到批量
    ///
    /// 如果达到批量大小或超时，返回准备好的批次
    pub fn push(&mut self, item: T) -> Option<Vec<T>> {
        self.items.push(item);

        if self.items.len() >= BATCH_SIZE || self.should_flush() {
            Some(self.flush())
        } else {
            None
        }
    }

    /// 检查是否应该刷新（超时）
    fn should_flush(&self) -> bool {
        self.last_flush.elapsed().as_millis() as u64 >= TIMEOUT_MS
    }

    /// 刷新并返回当前批次
    pub fn flush(&mut self) -> Vec<T> {
        let batch = std::mem::take(&mut self.items);
        self.items = Vec::with_capacity(BATCH_SIZE);
        self.last_flush = std::time::Instant::now();
        batch
    }

    /// 获取编译时批量大小
    pub const fn batch_size() -> usize {
        BATCH_SIZE
    }

    /// 获取编译时超时时间（毫秒）
    pub const fn timeout_ms() -> u64 {
        TIMEOUT_MS
    }

    /// 获取当前项目数量
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

impl<T, const BATCH_SIZE: usize, const TIMEOUT_MS: u64> Default 
    for TypedBatchProcessor<T, BATCH_SIZE, TIMEOUT_MS> {
    fn default() -> Self {
        Self::new()
    }
}

/// Generic Associated Types (GATs) 示例：类型化遥测处理器
///
/// GATs 允许在 trait 中定义带有生命周期参数的关联类型
pub trait TypedProcessor {
    /// 输入数据类型
    type Input;
    
    /// 输出数据类型（GAT - 可带生命周期）
    type Output<'a>: 'a
    where
        Self: 'a;
    
    /// 错误类型
    type Error;

    /// 处理输入数据，产生输出
    fn process(&self, input: Self::Input) -> Result<Self::Output<'_>, Self::Error>;
}

/// GATs 实现的遥测数据转换器
pub struct TelemetryConverter<F, T> {
    converter: Box<dyn Fn(F) -> T>,
}

impl<F, T> TelemetryConverter<F, T> {
    pub fn new<FN>(converter: FN) -> Self
    where
        FN: Fn(F) -> T + 'static,
    {
        Self {
            converter: Box::new(converter),
        }
    }
}

impl<F, T: Clone> TypedProcessor for TelemetryConverter<F, T> {
    type Input = F;
    type Output<'a> = T where Self: 'a;
    type Error = std::convert::Infallible;

    fn process(&self, input: Self::Input) -> Result<Self::Output<'_>, Self::Error> {
        Ok((self.converter)(input))
    }
}

/// GATs 实现的异步遥测流处理器
pub trait AsyncStreamProcessor {
    /// 输入项类型
    type Item;
    
    /// 输出流类型（GAT）
    type Stream<'a>: futures_core::Stream<Item = Self::Item> + 'a
    where
        Self: 'a;

    /// 处理流
    fn process_stream<'a>(&'a self, items: Vec<Self::Item>) -> Self::Stream<'a>;
}

/// 编译时确定的固定大小矩阵（用于指标计算）
#[derive(Debug, Clone)]
pub struct FixedMatrix<T, const ROWS: usize, const COLS: usize> {
    data: [[T; COLS]; ROWS],
}

impl<T: Copy + Default, const ROWS: usize, const COLS: usize> FixedMatrix<T, ROWS, COLS> {
    /// 创建新的固定大小矩阵
    pub fn new() -> Self {
        Self {
            data: [[T::default(); COLS]; ROWS],
        }
    }

    /// 使用初始化函数创建矩阵
    pub fn from_fn<F>(mut f: F) -> Self
    where
        F: FnMut(usize, usize) -> T,
    {
        let mut data = [[T::default(); COLS]; ROWS];
        for i in 0..ROWS {
            for j in 0..COLS {
                data[i][j] = f(i, j);
            }
        }
        Self { data }
    }

    /// 获取元素
    pub fn get(&self, row: usize, col: usize) -> Option<&T> {
        self.data.get(row)?.get(col)
    }

    /// 设置元素
    pub fn set(&mut self, row: usize, col: usize, value: T) -> bool {
        if let Some(cell) = self.data.get_mut(row).and_then(|r| r.get_mut(col)) {
            *cell = value;
            true
        } else {
            false
        }
    }

    /// 获取编译时行数
    pub const fn rows() -> usize {
        ROWS
    }

    /// 获取编译时列数
    pub const fn cols() -> usize {
        COLS
    }

    /// 转置矩阵（编译时维度交换）
    pub fn transpose(&self) -> FixedMatrix<T, COLS, ROWS> {
        FixedMatrix::from_fn(|i, j| self.data[j][i])
    }

    /// 映射矩阵元素
    pub fn map<U: Copy + Default, F>(&self, f: F) -> FixedMatrix<U, ROWS, COLS>
    where
        F: Fn(&T) -> U,
    {
        FixedMatrix::from_fn(|i, j| f(&self.data[i][j]))
    }
}

impl<T: Copy + Default, const ROWS: usize, const COLS: usize> Default 
    for FixedMatrix<T, ROWS, COLS> {
    fn default() -> Self {
        Self::new()
    }
}

/// 类型级别的遥测数据分类
///
/// 使用 const generics 实现编译时类型分类
pub struct ClassifiedTelemetry<T, const CATEGORY: u8> {
    data: T,
}

impl<T, const CATEGORY: u8> ClassifiedTelemetry<T, CATEGORY> {
    pub fn new(data: T) -> Self {
        Self { data }
    }

    pub fn into_inner(self) -> T {
        self.data
    }

    /// 获取编译时分类
    pub const fn category() -> TelemetryCategory {
        match CATEGORY {
            0 => TelemetryCategory::Trace,
            1 => TelemetryCategory::Metric,
            2 => TelemetryCategory::Log,
            3 => TelemetryCategory::Profile,
            _ => TelemetryCategory::Unknown,
        }
    }
}

/// 遥测数据分类枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TelemetryCategory {
    Trace = 0,
    Metric = 1,
    Log = 2,
    Profile = 3,
    Unknown = 255,
}

/// 类型别名：预定义的遥测分类
pub type TraceData<T> = ClassifiedTelemetry<T, 0>;
pub type MetricData<T> = ClassifiedTelemetry<T, 1>;
pub type LogData<T> = ClassifiedTelemetry<T, 2>;
pub type ProfileData<T> = ClassifiedTelemetry<T, 3>;

/// const fn 泛型 trait bounds 示例
///
/// Rust 1.61+ 支持在 const fn 中使用泛型 trait bounds
#[allow(dead_code)]
pub struct ConstGenericProcessor<T, P: Processor<T>> {
    processor: P,
    _phantom: PhantomData<T>,
}

pub trait Processor<T> {
    fn process(&self, item: T) -> T;
}

impl<T, P: Processor<T>> ConstGenericProcessor<T, P> {
    /// const fn 中使用泛型 trait bounds
    pub const fn new(processor: P) -> Self {
        Self {
            processor,
            _phantom: PhantomData,
        }
    }
}

/// 编译时计算的斐波那契数列（用于自适应批量大小）
pub struct Fibonacci;

impl Fibonacci {
    /// 编译时计算第 N 个斐波那契数
    pub const fn nth<const N: usize>() -> usize {
        Self::compute(N)
    }

    const fn compute(n: usize) -> usize {
        match n {
            0 => 0,
            1 => 1,
            _ => Self::compute(n - 1) + Self::compute(n - 2),
        }
    }

    /// 生成编译时斐波那契数组
    pub const fn array<const N: usize>() -> [usize; N] {
        let mut arr = [0usize; N];
        let mut i = 0;
        while i < N {
            arr[i] = Self::compute(i);
            i += 1;
        }
        arr
    }
}

/// 使用斐波那契数列的自适应批量大小计算器
pub struct FibonacciBatchSizer;

impl FibonacciBatchSizer {
    /// 根据重试次数获取批量大小
    ///
    /// 使用斐波那契数列实现指数退避的批量大小增长
    pub const fn batch_size_for_retry(retry_count: usize) -> usize {
        match retry_count {
            0 => 100,
            1 => 100,
            n if n <= 20 => Fibonacci::nth::<20>(),
            _ => 10000,
        }
    }
}

/// 编译时类型大小的断言（用于 FFI 兼容性检查）
#[macro_export]
macro_rules! const_assert_size {
    ($t:ty, $size:expr) => {
        const _: [(); $size] = [(); std::mem::size_of::<$t>()];
    };
}

/// 编译时对齐断言
#[macro_export]
macro_rules! const_assert_align {
    ($t:ty, $align:expr) => {
        const _: [(); $align] = [(); std::mem::align_of::<$t>()];
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ring_buffer() {
        let mut buffer: RingBuffer<i32, 4> = RingBuffer::new();
        assert_eq!(RingBuffer::<i32, 4>::capacity(), 4);
        
        buffer.push(1);
        buffer.push(2);
        buffer.push(3);
        
        assert_eq!(buffer.get(0), Some(&1));
        assert_eq!(buffer.get(1), Some(&2));
        
        buffer.push(4);
        buffer.push(5); // 这将覆盖 1
        
        assert_eq!(buffer.get(0), Some(&2)); // 1 被覆盖
        assert_eq!(buffer.get(3), Some(&5));
    }

    #[test]
    fn test_typed_batch_processor() {
        let mut processor: TypedBatchProcessor<String, 3, 1000> = TypedBatchProcessor::new();
        
        assert_eq!(TypedBatchProcessor::<String, 3, 1000>::batch_size(), 3);
        assert_eq!(TypedBatchProcessor::<String, 3, 1000>::timeout_ms(), 1000);
        
        assert!(processor.push("a".to_string()).is_none());
        assert!(processor.push("b".to_string()).is_none());
        
        let batch = processor.push("c".to_string());
        assert!(batch.is_some());
        assert_eq!(batch.unwrap().len(), 3);
    }

    #[test]
    fn test_fixed_matrix() {
        let matrix: FixedMatrix<i32, 3, 3> = FixedMatrix::from_fn(|i, j| (i * 3 + j) as i32);
        
        assert_eq!(FixedMatrix::<i32, 3, 3>::rows(), 3);
        assert_eq!(FixedMatrix::<i32, 3, 3>::cols(), 3);
        
        assert_eq!(matrix.get(0, 0), Some(&0));
        assert_eq!(matrix.get(1, 2), Some(&5));
        assert_eq!(matrix.get(2, 2), Some(&8));
        
        let transposed = matrix.transpose();
        assert_eq!(transposed.get(0, 1), Some(&3)); // 原矩阵 (1,0) 的值
    }

    #[test]
    fn test_classified_telemetry() {
        let trace: TraceData<String> = TraceData::new("trace data".to_string());
        let metric: MetricData<f64> = MetricData::new(42.0);
        
        assert_eq!(TraceData::<String>::category(), TelemetryCategory::Trace);
        assert_eq!(MetricData::<f64>::category(), TelemetryCategory::Metric);
        
        assert_eq!(trace.into_inner(), "trace data");
        assert_eq!(metric.into_inner(), 42.0);
    }

    #[test]
    fn test_fibonacci_const() {
        // 编译时计算
        const F10: usize = Fibonacci::nth::<10>();
        assert_eq!(F10, 55);
        
        const FIB_ARR: [usize; 10] = Fibonacci::array::<10>();
        assert_eq!(FIB_ARR, [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]);
    }

    #[test]
    fn test_telemetry_converter() {
        let converter = TelemetryConverter::new(|s: String| s.len());
        let result = converter.process("hello".to_string()).unwrap();
        assert_eq!(result, 5);
    }
}
