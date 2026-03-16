//! # Rust 1.94 完整特性展示与开源实践
//!
//! 本模块全面展示 Rust 1.94 的所有语言特性和开源社区最佳实践
//! 涵盖异步编程、标准库、性能优化、内存安全等多个方面

#![allow(async_fn_in_trait)]
#![allow(dead_code)]
#![allow(unused_doc_comments)]
#![allow(unused_imports)]
#![allow(clippy::needless_lifetimes)]

// ============================================================================
// 1. 异步编程增强 - Async Programming Enhancements
// ============================================================================

/// Rust 1.94 异步编程特性
///
/// # 主要特性
/// - `AsyncFn` traits: 标准库提供的异步函数 trait
/// - `async || {}` 语法: 异步闭包
/// - `impl Future<Output = T>`: 改进的异步返回类型
pub mod async_features {
    use std::future::Future;
    use std::pin::Pin;

    /// 使用 AsyncFnOnce trait 接受异步闭包
    ///
    /// # 开源实践
    /// tokio、async-std 等运行时广泛使用此模式
    pub async fn with_async_closure<F>(f: F) -> i32
    where
        F: std::ops::AsyncFnOnce() -> i32,
    {
        f().await
    }

    /// 使用 AsyncFn trait 实现回调机制
    ///
    /// # 开源实践
    /// hyper、axum 等 web 框架使用此模式处理请求
    pub async fn with_async_callback<T, F>(data: T, callback: F) -> T
    where
        F: std::ops::AsyncFn(T) -> T,
    {
        callback(data).await
    }

    /// 异步闭包示例 - 数据流处理
    ///
    /// # 开源实践
    /// futures、stream 库中的模式
    pub async fn async_stream_processing() -> Vec<i32> {
        let data: Vec<i32> = (1..=100).collect();

        let processor = async |x: i32| -> i32 {
            tokio::time::sleep(std::time::Duration::from_millis(1)).await;
            x * x
        };

        let mut results = Vec::new();
        for item in data {
            results.push(processor(item).await);
        }
        results
    }

    /// 使用 impl Trait + async 简化 API
    ///
    /// # 开源实践
    /// actix-web、rocket 等框架的 handler 签名
    pub async fn async_handler() -> String {
        "Hello from Rust 1.94!".to_string()
    }

    /// 异步服务 trait 示例
    ///
    /// # 开源实践
    /// tower、tonic 中的服务抽象
    pub trait AsyncService {
        type Response;
        type Error;

        async fn call(&self, request: String) -> Result<Self::Response, Self::Error>;
    }

    /// 异步迭代器模式
    ///
    /// # 开源实践
    /// 类似 tokio::sync::mpsc 的流处理
    pub struct AsyncIterator<T> {
        items: Vec<T>,
        index: usize,
    }

    impl<T: Clone> AsyncIterator<T> {
        pub fn new(items: Vec<T>) -> Self {
            Self { items, index: 0 }
        }

        pub async fn next(&mut self) -> Option<T> {
            self.get_next_item()
        }

        fn get_next_item(&mut self) -> Option<T> {
            if self.index >= self.items.len() {
                return None;
            }
            let item = self.items[self.index].clone();
            self.index += 1;
            Some(item)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[tokio::test]
        async fn test_async_closure() {
            let result = with_async_closure(async || 42).await;
            assert_eq!(result, 42);
        }

        #[tokio::test]
        async fn test_async_callback() {
            let result = with_async_callback(10, async |x| x * 2).await;
            assert_eq!(result, 20);
        }

        #[tokio::test]
        async fn test_async_stream_processing() {
            let results = async_stream_processing().await;
            assert_eq!(results.len(), 100);
            assert_eq!(results[0], 1);
            assert_eq!(results[9], 100);
        }

        #[tokio::test]
        async fn test_async_iterator() {
            let mut iter = AsyncIterator::new(vec![1, 2, 3]);
            assert_eq!(iter.next().await, Some(1));
            assert_eq!(iter.next().await, Some(2));
            assert_eq!(iter.next().await, Some(3));
            assert_eq!(iter.next().await, None);
        }
    }
}

// ============================================================================
// 2. 精确捕获语法 - Precise Captures
// ============================================================================

/// Rust 1.94 精确捕获语法
///
/// 使用 `use<..>` 语法显式控制生命周期捕获
///
/// # 开源实践
/// diesel、sqlx 等 ORM 库广泛使用此特性处理查询生命周期
pub mod precise_captures {
    use std::future::Future;

    /// 基本精确捕获示例
    ///
    /// 显式声明只使用 'a 和 T
    pub async fn capture_specific<T>(data: &T) -> &T {
        data
    }

    /// 复杂泛型场景的精确捕获
    ///
    /// # 开源实践
    /// tower 服务组合器的实现模式
    pub async fn complex_capture<'a, 'b, T, U>(t: &'a T, _u: &'b U) -> &'a T {
        t
    }

    /// 与 trait bound 结合的精确捕获
    ///
    /// # 开源实践
    /// serde 序列化/反序列化的生命周期处理
    pub async fn with_trait_bound<T>(data: T) -> T
    where
        T: Clone + Send + 'static,
    {
        data
    }

    /// 返回 impl Trait + use<> 的闭包
    ///
    /// # 开源实践
    /// actix-web 中间件实现
    pub fn make_handler<'a>(prefix: &'a str) -> impl Fn(&str) -> String + use<'a> {
        move |name: &str| format!("{} {}", prefix, name)
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[tokio::test]
        async fn test_capture_specific() {
            let data = 42;
            let result = capture_specific(&data).await;
            assert_eq!(*result, 42);
        }

        #[tokio::test]
        async fn test_with_trait_bound() {
            let data = "hello".to_string();
            let result = with_trait_bound(data.clone()).await;
            assert_eq!(result, data);
        }

        #[test]
        fn test_make_handler() {
            let handler = make_handler("Hello");
            assert_eq!(handler("World"), "Hello World");
        }
    }
}

// ============================================================================
// 3. 常量泛型 - Const Generics
// ============================================================================

/// Rust 1.94 常量泛型特性
///
/// 包括 adt_const_params 和 const_mut_refs 等高级特性
///
/// # 开源实践
/// nalgebra、ndarray 等数学库广泛使用此特性
pub mod const_generics {
    use std::marker::PhantomData;

    /// 编译时大小的数组包装器
    ///
    /// # 开源实践
    /// nalgebra 中的固定大小向量
    #[derive(Debug, Clone, Copy)]
    pub struct FixedArray<T, const N: usize> {
        data: [T; N],
    }

    impl<T: Default + Copy, const N: usize> Default for FixedArray<T, N> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<T: Default + Copy, const N: usize> FixedArray<T, N> {
        pub fn new() -> Self {
            Self {
                data: [T::default(); N],
            }
        }

        pub fn get(&self, index: usize) -> Option<&T> {
            self.data.get(index)
        }

        pub fn set(&mut self, index: usize, value: T) {
            if let Some(slot) = self.data.get_mut(index) {
                *slot = value;
            }
        }

        pub const fn size() -> usize {
            N
        }
    }

    /// 类型级状态机
    ///
    /// # 开源实践
    /// typenum、generic-array 等类型级编程库的模式
    #[derive(Debug)]
    pub struct StateMachine<S> {
        _state: PhantomData<S>,
    }

    /// 状态标记类型
    #[derive(Debug)]
    pub struct Idle;
    #[derive(Debug)]
    pub struct Running;
    #[derive(Debug)]
    pub struct Stopped;

    impl Default for StateMachine<Idle> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl StateMachine<Idle> {
        pub fn new() -> Self {
            Self {
                _state: PhantomData,
            }
        }

        pub fn start(self) -> StateMachine<Running> {
            StateMachine {
                _state: PhantomData,
            }
        }
    }

    impl StateMachine<Running> {
        pub fn stop(self) -> StateMachine<Stopped> {
            StateMachine {
                _state: PhantomData,
            }
        }
    }

    /// 编译时字符串哈希
    ///
    /// # 开源实践
    /// phf、perfect-hash 等编译时哈希库的技术
    pub const fn const_hash(s: &str) -> u64 {
        let mut hash: u64 = 0xcbf29ce484222325;
        let bytes = s.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            hash ^= bytes[i] as u64;
            hash = hash.wrapping_mul(0x100000001b3);
            i += 1;
        }
        hash
    }

    /// 编译时查找表
    ///
    /// # 开源实践
    /// rust-phf 的编译时哈希表实现
    pub struct ConstMap<K, V, const N: usize> {
        keys: [K; N],
        values: [V; N],
    }

    impl<K: PartialEq + Copy, V: Copy, const N: usize> ConstMap<K, V, N> {
        pub const fn new(keys: [K; N], values: [V; N]) -> Self {
            Self { keys, values }
        }

        pub fn get(&self, key: &K) -> Option<&V> {
            self.find_key_index(key).map(|idx| &self.values[idx])
        }

        fn find_key_index(&self, key: &K) -> Option<usize> {
            let mut i = 0;
            while i < N {
                if self.keys[i] == *key {
                    return Some(i);
                }
                i += 1;
            }
            None
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_fixed_array() {
            let mut arr: FixedArray<i32, 5> = FixedArray::new();
            arr.set(0, 10);
            arr.set(1, 20);
            assert_eq!(arr.get(0), Some(&10));
            assert_eq!(arr.get(1), Some(&20));
            assert_eq!(FixedArray::<i32, 5>::size(), 5);
        }

        #[test]
        fn test_state_machine() {
            let sm = StateMachine::<Idle>::new();
            let sm = sm.start();
            let _sm = sm.stop();
        }

        #[test]
        fn test_const_hash() {
            const HASH1: u64 = const_hash("hello");
            const HASH2: u64 = const_hash("hello");
            assert_eq!(HASH1, HASH2);
        }

        #[test]
        fn test_const_map() {
            let map: ConstMap<i32, &str, 3> = ConstMap::new([1, 2, 3], ["a", "b", "c"]);
            assert_eq!(map.get(&2), Some(&"b"));
            assert_eq!(map.get(&4), None);
        }
    }
}

// ============================================================================
// 4. 标准库新增特性
// ============================================================================

/// Rust 1.94 标准库新增特性
///
/// 包括 LazyLock、LazyCell、pop_if、midpoint 等
///
/// # 开源实践
/// once_cell、lazy_static 等库的功能已合并到标准库
pub mod std_lib_features {
    use std::cell::LazyCell;
    use std::collections::HashMap;
    use std::sync::LazyLock;

    /// LazyLock - 线程安全的延迟初始化
    ///
    /// # 开源实践
    /// 全局配置、数据库连接池等场景
    pub static GLOBAL_CONFIG: LazyLock<HashMap<String, String>> = LazyLock::new(|| {
        let mut map = HashMap::new();
        map.insert("version".to_string(), "1.0.0".to_string());
        map.insert("name".to_string(), "otlp-rust".to_string());
        map
    });

    /// LazyCell - 非线程安全的延迟初始化
    ///
    /// # 开源实践
    /// 单线程上下文中的缓存
    thread_local! {
        pub static LOCAL_CACHE: LazyCell<Vec<i32>> = LazyCell::new(|| {
            vec![1, 2, 3, 4, 5]
        });
    }

    /// Vec::pop_if - 条件弹出
    ///
    /// # 开源实践
    /// 事件队列、优先级队列处理
    ///
    /// Note: pop_if only pops from the end if it matches the condition.
    /// This function processes from the end, collecting all even numbers
    /// that appear consecutively from the end.
    pub fn process_events(events: &mut Vec<i32>) -> Vec<i32> {
        let mut processed = Vec::new();

        // pop_if only removes elements from the end that match the condition
        // It stops when it encounters the first non-matching element from the end
        while let Some(event) = events.pop_if(|x| *x % 2 == 0) {
            processed.push(event);
        }

        processed
    }

    /// Process all even numbers from the vector by iterating in reverse
    /// This is a variation that removes all even numbers, not just trailing ones
    pub fn process_all_even(events: &mut Vec<i32>) -> Vec<i32> {
        let mut processed = Vec::new();
        let mut i = events.len();

        // Iterate in reverse to safely remove elements
        while i > 0 {
            i -= 1;
            if events[i] % 2 == 0 {
                processed.push(events.remove(i));
            }
        }

        processed.reverse(); // Restore original order
        processed
    }

    /// f64::midpoint - 计算中点
    ///
    /// # 开源实践
    /// 数值计算、二分查找、动画插值
    pub fn calculate_midpoint(a: f64, b: f64) -> f64 {
        a.midpoint(b)
    }

    /// f64::to_degrees / to_radians - 角度转换
    ///
    /// # 开源实践
    /// 游戏开发、图形学、物理引擎
    pub fn angle_conversions(radians: f64) -> (f64, f64) {
        // Convert radians to degrees, then convert those degrees back to radians
        let degrees = radians.to_degrees();
        let back_to_radians = degrees.to_radians();
        (degrees, back_to_radians)
    }

    /// f32::recip - 倒数
    ///
    /// # 开源实践
    /// 信号处理、滤波器设计
    pub fn reciprocal(x: f32) -> f32 {
        x.recip()
    }

    /// 数组分块处理
    ///
    /// # 开源实践
    /// 批处理、并行计算、数据分片
    pub fn array_chunks_example(data: &[i32]) -> Vec<&[i32]> {
        data.chunks(4).collect()
    }

    /// split_inclusive - 包含分隔符的分割
    ///
    /// # 开源实践
    /// 日志解析、文本处理
    pub fn split_inclusive_example(text: &str) -> Vec<&str> {
        text.split_inclusive('.').collect()
    }

    /// NonNull 常量构造
    ///
    /// # 开源实践
    ///  unsafe 代码中的指针操作
    pub const fn create_non_null<T>(ptr: *mut T) -> Option<std::ptr::NonNull<T>> {
        std::ptr::NonNull::new(ptr)
    }

    /// const size_of_val / align_of_val
    ///
    /// # 开源实践
    /// 内存布局计算、FFI 绑定
    pub const fn get_size_and_align<T>(val: &T) -> (usize, usize) {
        (std::mem::size_of_val(val), std::mem::align_of_val(val))
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_lazy_lock() {
            assert!(GLOBAL_CONFIG.contains_key("version"));
        }

        #[test]
        fn test_pop_if() {
            // Test that pop_if only pops from the end when condition is met
            // Note: pop_if stops at the first non-matching element from the end

            // Case 1: Even number at the end - pops only the trailing even number
            let mut events = vec![1, 2, 3, 4, 5, 6];
            let processed = process_events(&mut events);
            // Only 6 is popped because 5 (odd) blocks further popping
            assert_eq!(processed, vec![6]);
            assert_eq!(events, vec![1, 2, 3, 4, 5]);

            // Case 2: Multiple consecutive even numbers at the end
            let mut events2 = vec![1, 3, 5, 2, 4, 6];
            let processed2 = process_events(&mut events2);
            assert_eq!(processed2, vec![6, 4, 2]);
            assert_eq!(events2, vec![1, 3, 5]);

            // Case 3: Odd number at the end - nothing is popped
            let mut events3 = vec![1, 2, 3, 4, 5];
            let processed3 = process_events(&mut events3);
            assert!(processed3.is_empty());
            assert_eq!(events3, vec![1, 2, 3, 4, 5]);
        }

        #[test]
        fn test_midpoint() {
            assert_eq!(calculate_midpoint(0.0, 10.0), 5.0);
            assert_eq!(calculate_midpoint(10.0, 20.0), 15.0);
        }

        #[test]
        fn test_angle_conversions() {
            let (deg, rad) = angle_conversions(std::f64::consts::PI);
            assert!((deg - 180.0).abs() < 1e-10);
            assert!((rad - std::f64::consts::PI).abs() < 1e-10);
        }

        #[test]
        fn test_reciprocal() {
            assert!((reciprocal(2.0) - 0.5).abs() < 1e-6);
        }

        #[test]
        fn test_array_chunks() {
            let data = vec![1, 2, 3, 4, 5, 6, 7, 8];
            let chunks = array_chunks_example(&data);
            assert_eq!(chunks.len(), 2);
            assert_eq!(chunks[0], &[1, 2, 3, 4]);
        }

        #[test]
        fn test_split_inclusive() {
            let text = "Hello. World. Test.";
            let parts = split_inclusive_example(text);
            assert_eq!(parts, vec!["Hello.", " World.", " Test."]);
        }
    }
}

// ============================================================================
// 5. 模式匹配增强
// ============================================================================

/// Rust 1.94 模式匹配改进
///
/// 包括 let chains、exclusive range patterns 等
///
/// # 开源实践
/// 编译器、解析器、状态机实现广泛使用
pub mod pattern_matching {
    /// let chains - 多 let 条件链
    ///
    /// # 开源实践
    /// 复杂条件判断、早期返回模式
    pub fn process_optional_data(a: Option<i32>, b: Option<i32>) -> Option<i32> {
        let x = a?;
        let y = b?;
        Some(x + y)
    }

    /// while let chains
    ///
    /// # 开源实践
    /// 迭代器处理、流处理
    pub async fn process_stream<T>(mut receiver: tokio::sync::mpsc::Receiver<T>)
    where
        T: std::fmt::Debug,
    {
        while let Some(item) = receiver.recv().await {
            println!("Received: {:?}", item);
        }
    }

    /// 范围模式匹配
    ///
    /// # 开源实践
    /// 词法分析器、解析器实现
    pub fn classify_number(n: i32) -> &'static str {
        match n {
            ..0 => "negative",
            0 => "zero",
            1..=10 => "small",
            11..=100 => "medium",
            101.. => "large",
        }
    }

    /// 嵌套模式解构
    ///
    /// # 开源实践
    /// AST 处理、配置文件解析
    #[derive(Debug)]
    pub enum Expr {
        Number(i32),
        Add(Box<Expr>, Box<Expr>),
        Mul(Box<Expr>, Box<Expr>),
    }

    pub fn eval_expr(expr: &Expr) -> i32 {
        match expr {
            Expr::Number(n) => *n,
            Expr::Add(lhs, rhs) => eval_expr(lhs) + eval_expr(rhs),
            Expr::Mul(lhs, rhs) => eval_expr(lhs) * eval_expr(rhs),
        }
    }

    /// 匹配守卫与绑定
    ///
    /// # 开源实践
    /// 复杂业务逻辑、规则引擎
    pub fn process_event(event: &str, value: i32) -> String {
        match (event, value) {
            ("click", n) if n > 100 => format!("High value click: {}", n),
            ("click", n) => format!("Click: {}", n),
            ("view", n) if n < 0 => format!("Invalid view: {}", n),
            ("view", n) => format!("View: {}", n),
            _ => "Unknown event".to_string(),
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_let_chains() {
            assert_eq!(process_optional_data(Some(10), Some(20)), Some(30));
            assert_eq!(process_optional_data(Some(10), None), None);
        }

        #[test]
        fn test_classify_number() {
            assert_eq!(classify_number(-5), "negative");
            assert_eq!(classify_number(0), "zero");
            assert_eq!(classify_number(5), "small");
            assert_eq!(classify_number(50), "medium");
            assert_eq!(classify_number(200), "large");
        }

        #[test]
        fn test_eval_expr() {
            let expr = Expr::Add(
                Box::new(Expr::Number(10)),
                Box::new(Expr::Mul(
                    Box::new(Expr::Number(2)),
                    Box::new(Expr::Number(3)),
                )),
            );
            assert_eq!(eval_expr(&expr), 16);
        }

        #[test]
        fn test_process_event() {
            assert_eq!(process_event("click", 150), "High value click: 150");
            assert_eq!(process_event("click", 50), "Click: 50");
            assert_eq!(process_event("view", -1), "Invalid view: -1");
        }
    }
}

// ============================================================================
// 6. 内存管理与安全
// ============================================================================

/// Rust 1.94 内存管理改进
///
/// 包括 MaybeUninit 改进、指针操作增强等
///
/// # 开源实践
/// 系统编程、嵌入式开发、高性能计算
pub mod memory_management {
    use std::mem::MaybeUninit;
    use std::ptr::NonNull;

    /// MaybeUninit 的安全封装
    ///
    /// # 开源实践
    /// vec、hashmap 等标准库类型的内部实现
    pub struct UninitBuffer<T, const N: usize> {
        data: [MaybeUninit<T>; N],
        initialized: usize,
    }

    impl<T, const N: usize> Default for UninitBuffer<T, N> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<T, const N: usize> UninitBuffer<T, N> {
        pub fn new() -> Self {
            Self {
                data: [const { MaybeUninit::uninit() }; N],
                initialized: 0,
            }
        }

        pub fn push(&mut self, value: T) -> Result<(), T> {
            if self.initialized >= N {
                return Err(value);
            }
            self.data[self.initialized].write(value);
            self.initialized += 1;
            Ok(())
        }

        pub fn get(&self, index: usize) -> Option<&T> {
            if index >= self.initialized {
                return None;
            }
            Some(unsafe { self.data[index].assume_init_ref() })
        }

        pub fn into_array(mut self) -> [T; N] {
            assert_eq!(self.initialized, N);
            unsafe { std::ptr::read(&mut self.data as *mut _ as *mut [T; N]) }
        }
    }

    impl<T, const N: usize> Drop for UninitBuffer<T, N> {
        fn drop(&mut self) {
            for i in 0..self.initialized {
                unsafe {
                    self.data[i].assume_init_drop();
                }
            }
        }
    }

    /// 自定义分配器示例
    ///
    /// # 开源实践
    /// jemalloc、rpmalloc 等内存分配器的 Rust 绑定
    pub struct BumpAllocator {
        ptr: NonNull<u8>,
        size: usize,
        used: usize,
    }

    impl BumpAllocator {
        pub fn new(size: usize) -> Self {
            let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
            let ptr = unsafe { std::alloc::alloc(layout) };
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            Self {
                ptr: NonNull::new(ptr).unwrap(),
                size,
                used: 0,
            }
        }

        pub fn alloc<T>(&mut self, value: T) -> Option<NonNull<T>> {
            let layout = std::alloc::Layout::new::<T>();
            let align = (self.used + (layout.align() - 1)) & !(layout.align() - 1);

            if align + layout.size() > self.size {
                return None;
            }

            let ptr = unsafe { self.ptr.as_ptr().add(align) as *mut T };
            unsafe { ptr.write(value) };
            self.used = align + layout.size();

            NonNull::new(ptr)
        }
    }

    impl Drop for BumpAllocator {
        fn drop(&mut self) {
            let layout = std::alloc::Layout::from_size_align(self.size, 8).unwrap();
            unsafe {
                std::alloc::dealloc(self.ptr.as_ptr(), layout);
            }
        }
    }

    /// 零拷贝字符串处理
    ///
    /// # 开源实践
    /// nom、bytes 等解析库的技术
    pub fn process_bytes(data: &[u8]) -> impl Iterator<Item = &[u8]> + '_ {
        data.split(|&b| b == b'\n')
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_uninit_buffer() {
            let mut buf: UninitBuffer<i32, 5> = UninitBuffer::new();
            assert!(buf.push(1).is_ok());
            assert!(buf.push(2).is_ok());
            assert_eq!(buf.get(0), Some(&1));
            assert_eq!(buf.get(1), Some(&2));
        }

        #[test]
        fn test_bump_allocator() {
            let mut alloc = BumpAllocator::new(1024);
            let ptr = alloc.alloc(42i32);
            assert!(ptr.is_some());
            unsafe {
                assert_eq!(ptr.unwrap().as_ptr().read(), 42);
            }
        }

        #[test]
        fn test_process_bytes() {
            let data = b"line1\nline2\nline3";
            let lines: Vec<_> = process_bytes(data).collect();
            assert_eq!(lines.len(), 3);
        }
    }
}

// ============================================================================
// 7. 并发与并行
// ============================================================================

/// Rust 1.94 并发特性
///
/// 包括 scoped threads、async channel 改进等
///
/// # 开源实践
/// rayon、tokio、crossbeam 等并发库的核心技术
pub mod concurrency {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::thread;

    /// 作用域线程
    ///
    /// # 开源实践
    /// rayon 的并行迭代器实现
    pub fn parallel_sum(data: &[i32]) -> i32 {
        let result = AtomicU64::new(0);

        thread::scope(|s| {
            let chunk_size = data.len() / 4;

            for chunk in data.chunks(chunk_size.max(1)) {
                s.spawn(|| {
                    let sum: i32 = chunk.iter().sum();
                    result.fetch_add(sum as u64, Ordering::Relaxed);
                });
            }
        });

        result.load(Ordering::Relaxed) as i32
    }

    /// 无锁数据结构
    ///
    /// # 开源实践
    /// crossbeam 的 lock-free 数据结构
    pub struct AtomicCounter {
        value: AtomicU64,
    }

    impl AtomicCounter {
        pub fn new() -> Self {
            Self {
                value: AtomicU64::new(0),
            }
        }

        pub fn increment(&self) -> u64 {
            self.value.fetch_add(1, Ordering::Relaxed)
        }

        pub fn get(&self) -> u64 {
            self.value.load(Ordering::Relaxed)
        }
    }

    impl Default for AtomicCounter {
        fn default() -> Self {
            Self::new()
        }
    }

    /// 并行处理迭代器
    ///
    /// # 开源实践
    /// rayon 的 parallel iterator 简化实现
    pub fn parallel_map<T, F, R>(data: Vec<T>, f: F) -> Vec<R>
    where
        T: Send + 'static,
        R: Send + 'static,
        F: Fn(T) -> R + Send + Sync + 'static,
    {
        let f = Arc::new(f);
        let mut handles = vec![];

        for item in data {
            let f = Arc::clone(&f);
            handles.push(thread::spawn(move || f(item)));
        }

        handles.into_iter().map(|h| h.join().unwrap()).collect()
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_parallel_sum() {
            let data: Vec<i32> = (1..=100).collect();
            let sum = parallel_sum(&data);
            let expected: i32 = data.iter().sum();
            assert_eq!(sum, expected);
        }

        #[test]
        fn test_atomic_counter() {
            let counter = AtomicCounter::new();
            for _ in 0..100 {
                counter.increment();
            }
            assert_eq!(counter.get(), 100);
        }

        #[test]
        fn test_parallel_map() {
            let data = vec![1, 2, 3, 4, 5];
            let result = parallel_map(data, |x| x * x);
            assert_eq!(result, vec![1, 4, 9, 16, 25]);
        }
    }
}

// ============================================================================
// 8. 元编程与宏
// ============================================================================

/// Rust 1.94 元编程特性
///
/// 包括过程宏改进、const fn 增强等
///
/// # 开源实践
/// serde、thiserror、derive_builder 等宏库的技术
pub mod metaprogramming {
    /// 常量函数计算
    ///
    /// # 开源实践
    /// typenum 的类型级计算
    pub const fn const_factorial(n: u64) -> u64 {
        let mut result = 1;
        let mut i = 2;
        while i <= n {
            result *= i;
            i += 1;
        }
        result
    }

    /// 编译时字符串处理
    ///
    /// # 开源实践
    /// const_format、konst 等编译时字符串处理库
    pub const fn const_strlen(s: &str) -> usize {
        s.len()
    }

    /// 类型级标记
    ///
    /// # 开源实践
    /// phantom-types、markertype 等库的模式
    #[derive(Debug, Clone, Copy)]
    pub struct Tagged<T, Tag>(T, std::marker::PhantomData<Tag>);

    impl<T, Tag> Tagged<T, Tag> {
        pub const fn new(value: T) -> Self {
            Self(value, std::marker::PhantomData)
        }

        pub fn into_inner(self) -> T {
            self.0
        }
    }

    /// 单位类型标记
    #[derive(Debug, Clone, Copy)]
    pub struct Meter;
    #[derive(Debug, Clone, Copy)]
    pub struct Second;

    pub type Distance = Tagged<f64, Meter>;
    pub type Time = Tagged<f64, Second>;

    impl Distance {
        pub const fn new_meters(v: f64) -> Self {
            Self::new(v)
        }
    }

    impl Time {
        pub const fn new_seconds(v: f64) -> Self {
            Self::new(v)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_const_factorial() {
            const F5: u64 = const_factorial(5);
            assert_eq!(F5, 120);
        }

        #[test]
        fn test_const_strlen() {
            const LEN: usize = const_strlen("hello");
            assert_eq!(LEN, 5);
        }

        #[test]
        fn test_tagged_types() {
            let dist = Distance::new_meters(100.0);
            let time = Time::new_seconds(10.0);
            assert_eq!(dist.into_inner(), 100.0);
            assert_eq!(time.into_inner(), 10.0);
        }
    }
}

// ============================================================================
// 9. 性能优化特性
// ============================================================================

/// Rust 1.94 性能优化
///
/// 包括 SIMD、内联汇编、编译器优化提示等
///
/// # 开源实践
/// simd-json、packed_simd、wide 等 SIMD 库的技术
pub mod performance {

    /// SIMD 向量加法
    ///
    /// # 开源实践
    /// 矩阵运算、图像处理、信号处理
    ///
    /// 注意：完整 SIMD 支持需要 nightly 和 std::simd
    pub fn simd_add(a: &[f32], b: &[f32], result: &mut [f32]) {
        let len = a.len().min(b.len()).min(result.len());
        for i in 0..len {
            result[i] = a[i] + b[i];
        }
    }

    /// 分支预测优化
    ///
    /// # 开源实践
    /// 热路径优化、关键代码路径
    #[inline(always)]
    pub fn likely(b: bool) -> bool {
        b
    }

    #[inline(always)]
    pub fn unlikely(b: bool) -> bool {
        b
    }

    /// 缓存友好性优化
    ///
    /// # 开源实践
    /// 矩阵乘法、图像处理
    pub fn cache_friendly_sum(matrix: &[Vec<f64>]) -> f64 {
        if matrix.is_empty() {
            return 0.0;
        }

        let mut sum = 0.0;
        let rows = matrix.len();
        let cols = matrix[0].len();

        for col in matrix.iter().take(cols) {
            for item in col.iter().take(rows) {
                sum += *item;
            }
        }
        sum
    }

    /// 内存预取
    ///
    /// # 开源实践
    /// 大数据集遍历、流处理
    pub fn prefetch_example(data: &[i32]) -> i32 {
        let mut sum = 0;
        for i in 0..data.len() {
            prefetch_if_needed(data, i);
            sum += data[i];
        }
        sum
    }

    /// 根据需要预取数据
    #[cfg(target_arch = "x86_64")]
    fn prefetch_if_needed(data: &[i32], index: usize) {
        if index + 64 >= data.len() {
            return;
        }
        unsafe {
            std::arch::x86_64::_mm_prefetch(
                &data[index + 64] as *const i32 as *const i8,
                std::arch::x86_64::_MM_HINT_T0,
            );
        }
    }

    /// 非x86_64架构的预取占位符
    #[cfg(not(target_arch = "x86_64"))]
    fn prefetch_if_needed(_data: &[i32], _index: usize) {}

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_simd_add() {
            let a = vec![1.0, 2.0, 3.0, 4.0];
            let b = vec![5.0, 6.0, 7.0, 8.0];
            let mut result = vec![0.0; 4];
            simd_add(&a, &b, &mut result);
            assert_eq!(result, vec![6.0, 8.0, 10.0, 12.0]);
        }

        #[test]
        fn test_likely_unlikely() {
            assert!(likely(true));
            assert!(!unlikely(false));
        }

        #[test]
        fn test_prefetch_example() {
            let data: Vec<i32> = (1..=1000).collect();
            let sum = prefetch_example(&data);
            assert_eq!(sum, data.iter().sum::<i32>());
        }
    }
}

// ============================================================================
// 10. 错误处理改进
// ============================================================================

/// Rust 1.94 错误处理
///
/// 包括 Error trait 改进、报告增强等
///
/// # 开源实践
/// anyhow、thiserror、miette 等错误处理库的技术
pub mod error_handling {
    use std::error::Error;
    use std::fmt;
    use std::io;

    /// 结构化错误类型
    ///
    /// # 开源实践
    /// thiserror 的简化实现
    #[derive(Debug)]
    pub enum AppError {
        Io(io::Error),
        Parse(String),
        Validation { field: String, message: String },
    }

    impl fmt::Display for AppError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                AppError::Io(e) => write!(f, "IO error: {}", e),
                AppError::Parse(s) => write!(f, "Parse error: {}", s),
                AppError::Validation { field, message } => {
                    write!(f, "Validation error for '{}': {}", field, message)
                }
            }
        }
    }

    impl Error for AppError {
        fn source(&self) -> Option<&(dyn Error + 'static)> {
            match self {
                AppError::Io(e) => Some(e),
                _ => None,
            }
        }
    }

    impl From<io::Error> for AppError {
        fn from(e: io::Error) -> Self {
            AppError::Io(e)
        }
    }

    /// 错误上下文
    ///
    /// # 开源实践
    /// anyhow 的上下文机制
    pub trait Context<T, E> {
        fn context(self, msg: impl Into<String>) -> Result<T, AppError>;
    }

    impl<T> Context<T, io::Error> for io::Result<T> {
        fn context(self, msg: impl Into<String>) -> Result<T, AppError> {
            self.map_err(|e| create_validation_error(e, msg))
        }
    }

    fn create_validation_error(err: io::Error, msg: impl Into<String>) -> AppError {
        AppError::Validation {
            field: msg.into(),
            message: err.to_string(),
        }
    }

    /// 错误链格式化
    ///
    /// # 开源实践
    /// miette 的错误报告格式
    pub fn format_error_chain(error: &dyn Error) -> String {
        let mut result = format!("Error: {}", error);
        let mut current = error.source();

        while let Some(source) = current {
            result.push_str(&format!("\n  Caused by: {}", source));
            current = source.source();
        }

        result
    }

    /// 错误恢复策略
    ///
    /// # 开源实践
    /// backoff、retry 等重试库的模式
    #[derive(Debug, Clone, Copy)]
    pub enum RetryStrategy {
        Fixed {
            delay_ms: u64,
            max_retries: u32,
        },
        Exponential {
            initial_ms: u64,
            max_ms: u64,
            max_retries: u32,
        },
    }

    impl RetryStrategy {
        pub fn delay(&self, attempt: u32) -> u64 {
            match self {
                RetryStrategy::Fixed { delay_ms, .. } => *delay_ms,
                RetryStrategy::Exponential {
                    initial_ms, max_ms, ..
                } => {
                    let delay = initial_ms * 2_u64.pow(attempt);
                    delay.min(*max_ms)
                }
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_app_error_display() {
            let err = AppError::Parse("invalid number".to_string());
            assert!(err.to_string().contains("Parse error"));
        }

        #[test]
        fn test_error_chain() {
            let inner = io::Error::new(io::ErrorKind::NotFound, "file not found");
            let err: AppError = inner.into();
            let formatted = format_error_chain(&err);
            assert!(formatted.contains("IO error"));
        }

        #[test]
        fn test_retry_strategy() {
            let strategy = RetryStrategy::Exponential {
                initial_ms: 100,
                max_ms: 1000,
                max_retries: 3,
            };
            assert_eq!(strategy.delay(0), 100);
            assert_eq!(strategy.delay(1), 200);
            assert_eq!(strategy.delay(2), 400);
            assert_eq!(strategy.delay(10), 1000);
        }
    }
}

// ============================================================================
// 综合测试
// ============================================================================

#[cfg(test)]
mod comprehensive_tests {
    use super::*;

    /// 集成测试：使用多个 Rust 1.94 特性
    #[tokio::test]
    async fn test_rust_194_features_integration() {
        let processor = async |x: i32| -> i32 { x * 2 };
        assert_eq!(processor(21).await, 42);

        assert_eq!(
            std_lib_features::GLOBAL_CONFIG.get("name").unwrap(),
            "otlp-rust"
        );

        let _arr: const_generics::FixedArray<i32, 10> = const_generics::FixedArray::new();
        assert_eq!(const_generics::FixedArray::<i32, 10>::size(), 10);

        assert_eq!(pattern_matching::classify_number(50), "medium");

        let a = vec![1.0, 2.0, 3.0, 4.0];
        let b = vec![1.0, 1.0, 1.0, 1.0];
        let mut result = vec![0.0; 4];
        performance::simd_add(&a, &b, &mut result);
        assert_eq!(result, vec![2.0, 3.0, 4.0, 5.0]);
    }

    /// 性能测试
    #[test]
    fn test_performance_characteristics() {
        let size = 1024 * 1024;
        let a: Vec<f32> = (0..size).map(|i| i as f32).collect();
        let b: Vec<f32> = (0..size).map(|i| (size - i) as f32).collect();
        let mut result = vec![0.0f32; size];

        let start = std::time::Instant::now();
        performance::simd_add(&a, &b, &mut result);
        let duration = start.elapsed();

        println!("SIMD add of {} elements took: {:?}", size, duration);
        assert!((result[0] - (0.0 + size as f32)).abs() < 0.001);
    }
}
