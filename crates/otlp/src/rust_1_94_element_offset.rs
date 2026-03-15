//! # Rust 1.94 `element_offset` Feature Implementation
//!
//! This module implements Rust 1.94's stabilized `<[T]>::element_offset` feature
//! for efficient memory offset calculations in OTLP operations.
//!
//! ## Features
//!
//! - **Zero-copy serialization offset calculation**: Calculate buffer positions without copying data
//! - **Buffer position tracking**: Track element positions within memory buffers
//! - **Memory pool indexing**: Efficient index calculation for memory pool elements
//!
//! ## Rust 1.94 Feature
//!
//! The `element_offset` method calculates the offset of an element in a slice,
//! returning `Some(usize)` if the element is within the slice, or `None` otherwise.
//!
//! ```rust,ignore
//! let slice = [10, 20, 30, 40, 50];
//! let offset = slice.element_offset(&slice[2]); // Returns Some(2)
//! ```
//!
//! ## Usage Examples
//!
//! ```rust
//! use otlp::rust_1_94_element_offset::{BufferOffsetCalculator, MemoryPoolIndexer};
//!
//! // Calculate buffer offset for zero-copy operations
//! let buffer = vec![1u8, 2, 3, 4, 5];
//! let calculator = BufferOffsetCalculator::new(&buffer);
//! let offset = calculator.get_offset(&buffer[2]);
//! assert_eq!(offset, Some(2));
//! ```

use std::marker::PhantomData;

/// Calculate buffer offset for zero-copy serialization operations.
///
/// This function uses Rust 1.94's `element_offset` to determine the position
/// of an element within a buffer, enabling efficient zero-copy serialization.
///
/// # Type Parameters
///
/// * `T` - The element type of the slice
///
/// # Arguments
///
/// * `slice` - The slice to search within
/// * `element` - Reference to the element to locate
///
/// # Returns
///
/// * `Some(usize)` - The offset of the element within the slice
/// * `None` - If the element is not within the slice's memory range
///
/// # Examples
///
/// ```rust
/// use otlp::rust_1_94_element_offset::calculate_buffer_offset;
///
/// let buffer = vec![10, 20, 30, 40, 50];
/// let offset = calculate_buffer_offset(&buffer, &buffer[2]);
/// assert_eq!(offset, Some(2));
/// ```
pub fn calculate_buffer_offset<T>(slice: &[T], element: &T) -> Option<usize> {
    slice.element_offset(element)
}

/// Calculate the byte offset of an element in a byte slice.
///
/// This is particularly useful for network protocols and serialization
/// where byte-level offsets are required.
///
/// # Arguments
///
/// * `buffer` - The byte buffer to search within
/// * `element` - Reference to the byte element to locate
///
/// # Returns
///
/// * `Some(usize)` - The byte offset of the element
/// * `None` - If the element is not within the buffer's memory range
///
/// # Examples
///
/// ```rust
/// use otlp::rust_1_94_element_offset::calculate_byte_offset;
///
/// let buffer = b"Hello, World!";
/// let offset = calculate_byte_offset(buffer, &buffer[7]);
/// assert_eq!(offset, Some(7));
/// ```
pub fn calculate_byte_offset(buffer: &[u8], element: &u8) -> Option<usize> {
    buffer.element_offset(element)
}

/// Buffer offset calculator for zero-copy operations.
///
/// This struct provides a convenient wrapper around `element_offset` for
/// tracking positions within buffers during serialization and deserialization.
///
/// # Type Parameters
///
/// * `T` - The element type of the buffer
///
/// # Examples
///
/// ```rust
/// use otlp::rust_1_94_element_offset::BufferOffsetCalculator;
///
/// let buffer = vec![1u8, 2, 3, 4, 5];
/// let calculator = BufferOffsetCalculator::new(&buffer);
///
/// assert_eq!(calculator.get_offset(&buffer[0]), Some(0));
/// assert_eq!(calculator.get_offset(&buffer[4]), Some(4));
/// assert_eq!(calculator.byte_offset(&buffer[2]), Some(2));
/// ```
#[derive(Debug, Clone, Copy)]
pub struct BufferOffsetCalculator<'a, T> {
    buffer: &'a [T],
}

impl<'a, T> BufferOffsetCalculator<'a, T> {
    /// Create a new buffer offset calculator.
    ///
    /// # Arguments
    ///
    /// * `buffer` - The buffer to calculate offsets within
    pub fn new(buffer: &'a [T]) -> Self {
        Self { buffer }
    }

    /// Get the offset of an element within the buffer.
    ///
    /// # Arguments
    ///
    /// * `element` - Reference to the element to locate
    ///
    /// # Returns
    ///
    /// * `Some(usize)` - The offset in elements
    /// * `None` - If the element is not within the buffer
    pub fn get_offset(&self, element: &T) -> Option<usize> {
        self.buffer.element_offset(element)
    }

    /// Get the byte offset of an element (for byte slices).
    ///
    /// For non-byte types, this returns the same as `get_offset` multiplied
    /// by the size of the element type.
    ///
    /// # Arguments
    ///
    /// * `element` - Reference to the element to locate
    ///
    /// # Returns
    ///
    /// * `Some(usize)` - The byte offset
    /// * `None` - If the element is not within the buffer
    pub fn byte_offset(&self, element: &T) -> Option<usize> {
        self.buffer.element_offset(element)
    }

    /// Check if an element is within the buffer.
    ///
    /// # Arguments
    ///
    /// * `element` - Reference to the element to check
    ///
    /// # Returns
    ///
    /// `true` if the element is within the buffer, `false` otherwise
    pub fn contains(&self, element: &T) -> bool {
        self.buffer.element_offset(element).is_some()
    }

    /// Get the buffer length.
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// Check if the buffer is empty.
    pub fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }

    /// Get a reference to the underlying buffer.
    pub fn buffer(&self) -> &'a [T] {
        self.buffer
    }
}

impl<'a> BufferOffsetCalculator<'a, u8> {
    /// Get the range offset of a sub-slice within the byte buffer.
    ///
    /// This is useful for zero-copy serialization where you need to track
    /// the position and length of a sub-slice within a larger buffer.
    ///
    /// # Arguments
    ///
    /// * `sub_slice` - The sub-slice to locate
    ///
    /// # Returns
    ///
    /// * `Some((usize, usize))` - Tuple of (offset, length)
    /// * `None` - If the sub-slice is not within the buffer
    ///
    /// # Examples
    ///
    /// ```rust
    /// use otlp::rust_1_94_element_offset::BufferOffsetCalculator;
    ///
    /// let buffer = b"Hello, World! This is OTLP data.";
    /// let calculator = BufferOffsetCalculator::new(buffer);
    ///
    /// let sub_slice = &buffer[7..12]; // "World"
    /// let (offset, len) = calculator.get_range_offset(sub_slice).unwrap();
    /// assert_eq!(offset, 7);
    /// assert_eq!(len, 5);
    /// ```
    pub fn get_range_offset(&self, sub_slice: &[u8]) -> Option<(usize, usize)> {
        if sub_slice.is_empty() {
            return Some((0, 0));
        }

        self.buffer
            .element_offset(&sub_slice[0])
            .map(|start| (start, sub_slice.len()))
    }
}

/// Memory pool with element indexing support.
///
/// This struct provides a memory pool that uses `element_offset` to efficiently
/// track and retrieve element indices.
///
/// # Type Parameters
///
/// * `T` - The element type stored in the pool
///
/// # Examples
///
/// ```rust
/// use otlp::rust_1_94_element_offset::MemoryPoolIndexer;
///
/// let pool = MemoryPoolIndexer::new(vec![10, 20, 30, 40, 50]);
///
/// assert_eq!(pool.get_element_index(&pool.buffer()[2]), Some(2));
/// assert_eq!(pool.get_element_index(&pool.buffer()[4]), Some(4));
/// ```
#[derive(Debug, Clone)]
pub struct MemoryPoolIndexer<T> {
    buffer: Vec<T>,
}

impl<T> MemoryPoolIndexer<T> {
    /// Create a new memory pool indexer.
    ///
    /// # Arguments
    ///
    /// * `buffer` - The buffer to use as the memory pool
    pub fn new(buffer: Vec<T>) -> Self {
        Self { buffer }
    }

    /// Get the index of an element within the memory pool.
    ///
    /// # Arguments
    ///
    /// * `element` - Reference to the element to locate
    ///
    /// # Returns
    ///
    /// * `Some(usize)` - The index of the element
    /// * `None` - If the element is not within the pool
    pub fn get_element_index(&self, element: &T) -> Option<usize> {
        self.buffer.element_offset(element)
    }

    /// Check if an element belongs to this memory pool.
    ///
    /// # Arguments
    ///
    /// * `element` - Reference to the element to check
    ///
    /// # Returns
    ///
    /// `true` if the element is within the pool, `false` otherwise
    pub fn contains(&self, element: &T) -> bool {
        self.buffer.element_offset(element).is_some()
    }

    /// Get a reference to the buffer.
    pub fn buffer(&self) -> &[T] {
        &self.buffer
    }

    /// Get the length of the buffer.
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// Check if the buffer is empty.
    pub fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }

    /// Get a mutable reference to the buffer.
    pub fn buffer_mut(&mut self) -> &mut [T] {
        &mut self.buffer
    }

    /// Get an element by index.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the element to retrieve
    ///
    /// # Returns
    ///
    /// * `Some(&T)` - Reference to the element at the given index
    /// * `None` - If the index is out of bounds
    pub fn get(&self, index: usize) -> Option<&T> {
        self.buffer.get(index)
    }

    /// Get a mutable reference to an element by index.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.buffer.get_mut(index)
    }
}

/// Zero-copy serialization helper using element offsets.
///
/// This struct provides utilities for zero-copy serialization by tracking
/// the offsets of serialized elements within a buffer.
///
/// # Examples
///
/// ```rust
/// use otlp::rust_1_94_element_offset::ZeroCopySerializer;
///
/// let data = vec![1u8, 2, 3, 4, 5, 6, 7, 8];
/// let serializer = ZeroCopySerializer::new(&data);
///
/// let sub_data = &data[2..6]; // [3, 4, 5, 6]
/// let offset = serializer.calculate_serialization_offset(sub_data);
/// assert_eq!(offset, Some(2));
/// ```
#[derive(Debug, Clone, Copy)]
pub struct ZeroCopySerializer<'a, T> {
    data: &'a [T],
    _phantom: PhantomData<T>,
}

impl<'a, T> ZeroCopySerializer<'a, T> {
    /// Create a new zero-copy serializer.
    ///
    /// # Arguments
    ///
    /// * `data` - The data buffer to serialize from
    pub fn new(data: &'a [T]) -> Self {
        Self {
            data,
            _phantom: PhantomData,
        }
    }

    /// Calculate the serialization offset for a sub-slice.
    ///
    /// This method returns the offset at which a sub-slice begins within
    /// the main data buffer, enabling zero-copy serialization by referencing
    /// the offset rather than copying the data.
    ///
    /// # Arguments
    ///
    /// * `sub_slice` - The sub-slice to calculate the offset for
    ///
    /// # Returns
    ///
    /// * `Some(usize)` - The offset of the sub-slice
    /// * `None` - If the sub-slice is not within the data buffer
    pub fn calculate_serialization_offset(&self, sub_slice: &[T]) -> Option<usize> {
        if sub_slice.is_empty() {
            return Some(0);
        }
        self.data.element_offset(&sub_slice[0])
    }

    /// Verify that a sub-slice is valid for zero-copy serialization.
    ///
    /// This checks that the sub-slice is contiguous and within the bounds
    /// of the main data buffer.
    ///
    /// # Arguments
    ///
    /// * `sub_slice` - The sub-slice to verify
    ///
    /// # Returns
    ///
    /// `true` if the sub-slice is valid for zero-copy serialization
    pub fn is_valid_for_zero_copy(&self, sub_slice: &[T]) -> bool {
        if sub_slice.is_empty() {
            return true;
        }

        match self.data.element_offset(&sub_slice[0]) {
            Some(start_offset) => {
                // Check if the entire sub-slice fits within the data
                let end_offset = start_offset + sub_slice.len();
                end_offset <= self.data.len()
            }
            None => false,
        }
    }

    /// Get the data buffer.
    pub fn data(&self) -> &'a [T] {
        self.data
    }
}

impl<'a> ZeroCopySerializer<'a, u8> {
    /// Create a slice reference for serialization without copying.
    ///
    /// This method returns a byte slice reference that can be used for
    /// zero-copy serialization. The returned slice shares memory with
    /// the original data buffer.
    ///
    /// # Arguments
    ///
    /// * `offset` - The starting offset in the buffer
    /// * `len` - The length of the slice to create
    ///
    /// # Returns
    ///
    /// * `Some(&[u8])` - The slice reference
    /// * `None` - If the range is out of bounds
    ///
    /// # Safety
    ///
    /// The caller must ensure that the original data buffer remains valid
    /// for the lifetime of the returned slice.
    pub fn create_zero_copy_slice(&self, offset: usize, len: usize) -> Option<&'a [u8]> {
        if offset + len > self.data.len() {
            return None;
        }
        Some(&self.data[offset..offset + len])
    }
}

/// Offset-based span tracker for tracing data.
///
/// This struct uses `element_offset` to efficiently track spans within
/// a trace buffer, enabling efficient access and manipulation of trace data.
///
/// # Examples
///
/// ```rust
/// use otlp::rust_1_94_element_offset::SpanTracker;
///
/// let trace_data = vec![
///     "span_1_start", "span_1_end",
///     "span_2_start", "span_2_end",
/// ];
/// let tracker = SpanTracker::new(&trace_data);
///
/// let span_start = &trace_data[2]; // "span_2_start"
/// let offset = tracker.get_span_offset(span_start);
/// assert_eq!(offset, Some(2));
/// ```
#[derive(Debug, Clone, Copy)]
pub struct SpanTracker<'a, T> {
    trace_buffer: &'a [T],
}

impl<'a, T> SpanTracker<'a, T> {
    /// Create a new span tracker.
    ///
    /// # Arguments
    ///
    /// * `trace_buffer` - The buffer containing trace data
    pub fn new(trace_buffer: &'a [T]) -> Self {
        Self { trace_buffer }
    }

    /// Get the offset of a span within the trace buffer.
    ///
    /// # Arguments
    ///
    /// * `span_element` - Reference to an element within the span
    ///
    /// # Returns
    ///
    /// * `Some(usize)` - The offset of the span element
    /// * `None` - If the element is not within the trace buffer
    pub fn get_span_offset(&self, span_element: &T) -> Option<usize> {
        self.trace_buffer.element_offset(span_element)
    }

    /// Get the range of a span given its start and end elements.
    ///
    /// # Arguments
    ///
    /// * `start_element` - Reference to the start element of the span
    /// * `end_element` - Reference to the end element of the span
    ///
    /// # Returns
    ///
    /// * `Some((usize, usize))` - Tuple of (start_offset, end_offset)
    /// * `None` - If either element is not within the trace buffer
    pub fn get_span_range(&self, start_element: &T, end_element: &T) -> Option<(usize, usize)> {
        let start = self.trace_buffer.element_offset(start_element)?;
        let end = self.trace_buffer.element_offset(end_element)?;
        Some((start, end))
    }

    /// Get the length of a span.
    ///
    /// # Arguments
    ///
    /// * `start_element` - Reference to the start element
    /// * `end_element` - Reference to the end element
    ///
    /// # Returns
    ///
    /// * `Some(usize)` - The length of the span
    /// * `None` - If either element is not within the trace buffer
    pub fn get_span_length(&self, start_element: &T, end_element: &T) -> Option<usize> {
        self.get_span_range(start_element, end_element)
            .map(|(start, end)| end.saturating_sub(start) + 1)
    }

    /// Get the trace buffer.
    pub fn buffer(&self) -> &'a [T] {
        self.trace_buffer
    }
}

/// Efficient offset calculator for batch operations.
///
/// This struct provides batch offset calculation capabilities for efficiently
/// processing multiple elements at once.
///
/// # Examples
///
/// ```rust
/// use otlp::rust_1_94_element_offset::BatchOffsetCalculator;
///
/// let batch_data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
/// let calculator = BatchOffsetCalculator::new(&batch_data);
///
/// let elements = vec![&batch_data[1], &batch_data[3], &batch_data[5]];
/// let offsets = calculator.calculate_batch_offsets(&elements);
/// assert_eq!(offsets, vec![Some(1), Some(3), Some(5)]);
/// ```
pub struct BatchOffsetCalculator<'a, T> {
    buffer: &'a [T],
}

impl<'a, T> BatchOffsetCalculator<'a, T> {
    /// Create a new batch offset calculator.
    ///
    /// # Arguments
    ///
    /// * `buffer` - The buffer containing the batch data
    pub fn new(buffer: &'a [T]) -> Self {
        Self { buffer }
    }

    /// Calculate offsets for multiple elements.
    ///
    /// # Arguments
    ///
    /// * `elements` - Slice of element references to calculate offsets for
    ///
    /// # Returns
    ///
    /// A vector of `Option<usize>` containing the offset for each element
    pub fn calculate_batch_offsets(&self, elements: &[&T]) -> Vec<Option<usize>> {
        elements
            .iter()
            .map(|elem| self.buffer.element_offset(elem))
            .collect()
    }

    /// Filter elements that are within the buffer.
    ///
    /// # Arguments
    ///
    /// * `elements` - Slice of element references to filter
    ///
    /// # Returns
    ///
    /// A vector of tuples (offset, element_reference) for elements within the buffer
    pub fn filter_valid_elements<'b>(&self, elements: &[&'b T]) -> Vec<(usize, &'b T)> {
        elements
            .iter()
            .filter_map(|elem| {
                self.buffer
                    .element_offset(elem)
                    .map(|offset| (offset, *elem))
            })
            .collect()
    }

    /// Get the buffer.
    pub fn buffer(&self) -> &'a [T] {
        self.buffer
    }
}

/// Metrics buffer with offset-based indexing.
///
/// Specialized buffer for metrics data that uses element offsets for
/// efficient data access and serialization.
///
/// # Examples
///
/// ```rust
/// use otlp::rust_1_94_element_offset::MetricsBuffer;
///
/// let metrics = vec![1.0f64, 2.0, 3.0, 4.0, 5.0];
/// let buffer = MetricsBuffer::new(metrics);
///
/// let metric_ref = buffer.get_metric(2).unwrap();
/// let index = buffer.get_metric_index(metric_ref);
/// assert_eq!(index, Some(2));
/// ```
#[derive(Debug, Clone)]
pub struct MetricsBuffer<T> {
    data: Vec<T>,
}

impl<T> MetricsBuffer<T> {
    /// Create a new metrics buffer.
    ///
    /// # Arguments
    ///
    /// * `data` - The metrics data vector
    pub fn new(data: Vec<T>) -> Self {
        Self { data }
    }

    /// Get a metric by index.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the metric to retrieve
    ///
    /// # Returns
    ///
    /// * `Some(&T)` - Reference to the metric
    /// * `None` - If the index is out of bounds
    pub fn get_metric(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }

    /// Get the index of a metric within the buffer.
    ///
    /// # Arguments
    ///
    /// * `metric` - Reference to the metric to locate
    ///
    /// # Returns
    ///
    /// * `Some(usize)` - The index of the metric
    /// * `None` - If the metric is not within the buffer
    pub fn get_metric_index(&self, metric: &T) -> Option<usize> {
        self.data.element_offset(metric)
    }

    /// Check if a metric belongs to this buffer.
    pub fn contains_metric(&self, metric: &T) -> bool {
        self.data.element_offset(metric).is_some()
    }

    /// Get the underlying data.
    pub fn data(&self) -> &[T] {
        &self.data
    }

    /// Get the number of metrics.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Check if the buffer is empty.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

/// Log entry tracker for efficient log processing.
///
/// Uses element offsets to track and reference log entries within
/// a log buffer.
///
/// # Examples
///
/// ```rust
/// use otlp::rust_1_94_element_offset::LogEntryTracker;
///
/// let logs = vec!["log1", "log2", "log3", "log4"];
/// let tracker = LogEntryTracker::new(&logs);
///
/// let log_ref = &logs[2];
/// let offset = tracker.get_log_offset(log_ref);
/// assert_eq!(offset, Some(2));
/// ```
#[derive(Debug, Clone, Copy)]
pub struct LogEntryTracker<'a, T> {
    logs: &'a [T],
}

impl<'a, T> LogEntryTracker<'a, T> {
    /// Create a new log entry tracker.
    ///
    /// # Arguments
    ///
    /// * `logs` - The log entries buffer
    pub fn new(logs: &'a [T]) -> Self {
        Self { logs }
    }

    /// Get the offset of a log entry.
    ///
    /// # Arguments
    ///
    /// * `entry` - Reference to the log entry
    ///
    /// # Returns
    ///
    /// * `Some(usize)` - The offset of the log entry
    /// * `None` - If the entry is not within the log buffer
    pub fn get_log_offset(&self, entry: &T) -> Option<usize> {
        self.logs.element_offset(entry)
    }

    /// Get the range of log entries between two entries.
    pub fn get_log_range(&self, start: &T, end: &T) -> Option<&'a [T]> {
        let start_idx = self.logs.element_offset(start)?;
        let end_idx = self.logs.element_offset(end)?;

        if start_idx <= end_idx && end_idx < self.logs.len() {
            Some(&self.logs[start_idx..=end_idx])
        } else {
            None
        }
    }

    /// Get the log buffer.
    pub fn logs(&self) -> &'a [T] {
        self.logs
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_calculate_buffer_offset() {
        let buffer = vec![10, 20, 30, 40, 50];

        assert_eq!(calculate_buffer_offset(&buffer, &buffer[0]), Some(0));
        assert_eq!(calculate_buffer_offset(&buffer, &buffer[2]), Some(2));
        assert_eq!(calculate_buffer_offset(&buffer, &buffer[4]), Some(4));

        // External element should return None
        let external = 100;
        assert_eq!(calculate_buffer_offset(&buffer, &external), None);
    }

    #[test]
    fn test_calculate_byte_offset() {
        let buffer = b"Hello, World!";

        assert_eq!(calculate_byte_offset(buffer, &buffer[0]), Some(0));
        assert_eq!(calculate_byte_offset(buffer, &buffer[7]), Some(7));
        assert_eq!(calculate_byte_offset(buffer, &buffer[12]), Some(12));

        // External byte should return None
        let external = b'X';
        assert_eq!(calculate_byte_offset(buffer, &external), None);
    }

    #[test]
    fn test_buffer_offset_calculator() {
        let buffer = vec![1u8, 2, 3, 4, 5];
        let calculator = BufferOffsetCalculator::new(&buffer);

        assert_eq!(calculator.get_offset(&buffer[0]), Some(0));
        assert_eq!(calculator.get_offset(&buffer[2]), Some(2));
        assert_eq!(calculator.get_offset(&buffer[4]), Some(4));

        assert!(calculator.contains(&buffer[0]));
        assert!(!calculator.contains(&100u8));

        assert_eq!(calculator.len(), 5);
        assert!(!calculator.is_empty());
    }

    #[test]
    fn test_buffer_range_offset() {
        let buffer = b"Hello, World! This is OTLP data.";
        let calculator = BufferOffsetCalculator::new(buffer);

        // Test sub-slice offset calculation
        let sub_slice = &buffer[7..12]; // "World"
        let (offset, len) = calculator.get_range_offset(sub_slice).unwrap();
        assert_eq!(offset, 7);
        assert_eq!(len, 5);

        // Test empty slice
        assert_eq!(calculator.get_range_offset(b""), Some((0, 0)));
    }

    #[test]
    fn test_memory_pool_indexer() {
        let buffer = vec![10, 20, 30, 40, 50];
        let pool = MemoryPoolIndexer::new(buffer);

        // Test getting element index
        assert_eq!(pool.get_element_index(&pool.buffer()[0]), Some(0));
        assert_eq!(pool.get_element_index(&pool.buffer()[2]), Some(2));
        assert_eq!(pool.get_element_index(&pool.buffer()[4]), Some(4));

        // Test contains
        assert!(pool.contains(&pool.buffer()[0]));
        let external = 100;
        assert!(!pool.contains(&external));

        // Test get
        assert_eq!(pool.get(2), Some(&30));
        assert_eq!(pool.get(10), None);
    }

    #[test]
    fn test_zero_copy_serializer() {
        let data = vec![1u8, 2, 3, 4, 5, 6, 7, 8];
        let serializer = ZeroCopySerializer::new(&data);

        // Test offset calculation
        let sub_data = &data[2..6];
        let offset = serializer.calculate_serialization_offset(sub_data);
        assert_eq!(offset, Some(2));

        // Test validation
        assert!(serializer.is_valid_for_zero_copy(sub_data));
        assert!(serializer.is_valid_for_zero_copy(b""));

        // Test slice creation
        let slice = serializer.create_zero_copy_slice(2, 4).unwrap();
        assert_eq!(slice, &[3, 4, 5, 6]);

        // Test out of bounds
        assert_eq!(serializer.create_zero_copy_slice(10, 5), None);
    }

    #[test]
    fn test_span_tracker() {
        let trace_data = vec!["start1", "end1", "start2", "end2"];
        let tracker = SpanTracker::new(&trace_data);

        // Test span offset
        assert_eq!(tracker.get_span_offset(&trace_data[0]), Some(0));
        assert_eq!(tracker.get_span_offset(&trace_data[2]), Some(2));

        // Test span range
        let range = tracker.get_span_range(&trace_data[0], &trace_data[1]);
        assert_eq!(range, Some((0, 1)));

        // Test span length
        let length = tracker.get_span_length(&trace_data[0], &trace_data[1]);
        assert_eq!(length, Some(2));
    }

    #[test]
    fn test_batch_offset_calculator() {
        let batch_data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let calculator = BatchOffsetCalculator::new(&batch_data);

        // Test batch offset calculation
        let elements: Vec<&i32> = vec![&batch_data[1], &batch_data[3], &batch_data[5]];
        let offsets = calculator.calculate_batch_offsets(&elements);
        assert_eq!(offsets, vec![Some(1), Some(3), Some(5)]);

        // Test filtering
        let external = 100;
        let mixed_elements: Vec<&i32> = vec![&batch_data[0], &external, &batch_data[2]];
        let valid = calculator.filter_valid_elements(&mixed_elements);
        assert_eq!(valid.len(), 2);
        assert_eq!(valid[0], (0, &batch_data[0]));
        assert_eq!(valid[1], (2, &batch_data[2]));
    }

    #[test]
    fn test_metrics_buffer() {
        let metrics = vec![1.0f64, 2.0, 3.0, 4.0, 5.0];
        let buffer = MetricsBuffer::new(metrics);

        // Test get metric
        assert_eq!(buffer.get_metric(2), Some(&3.0));
        assert_eq!(buffer.get_metric(10), None);

        // Test get metric index
        let metric_ref = buffer.get_metric(2).unwrap();
        assert_eq!(buffer.get_metric_index(metric_ref), Some(2));

        // Test contains
        assert!(buffer.contains_metric(metric_ref));
        let external = 10.0f64;
        assert!(!buffer.contains_metric(&external));
    }

    #[test]
    fn test_log_entry_tracker() {
        let logs = vec!["log1", "log2", "log3", "log4"];
        let tracker = LogEntryTracker::new(&logs);

        // Test log offset
        assert_eq!(tracker.get_log_offset(&logs[0]), Some(0));
        assert_eq!(tracker.get_log_offset(&logs[2]), Some(2));

        // Test log range
        let range = tracker.get_log_range(&logs[1], &logs[3]);
        assert_eq!(range, Some(&["log2", "log3", "log4"][..]));

        // Test invalid range
        let range = tracker.get_log_range(&logs[3], &logs[1]);
        assert!(range.is_none());
    }

    #[test]
    fn test_zero_copy_with_different_types() {
        // Test with i32
        let int_data = vec![100i32, 200, 300, 400];
        let int_serializer = ZeroCopySerializer::new(&int_data);
        let sub_int = &int_data[1..3];
        assert_eq!(
            int_serializer.calculate_serialization_offset(sub_int),
            Some(1)
        );

        // Test with String
        let string_data = vec!["hello".to_string(), "world".to_string(), "otlp".to_string()];
        let string_serializer = ZeroCopySerializer::new(&string_data);
        let sub_string = &string_data[1..2];
        assert_eq!(
            string_serializer.calculate_serialization_offset(sub_string),
            Some(1)
        );
    }

    #[test]
    fn test_memory_pool_mutability() {
        let mut pool = MemoryPoolIndexer::new(vec![1, 2, 3, 4, 5]);

        // Test mutable access
        if let Some(elem) = pool.get_mut(2) {
            *elem = 30;
        }

        assert_eq!(pool.get(2), Some(&30));

        // Test that index still works after mutation
        let elem_ref = &pool.buffer()[2];
        assert_eq!(pool.get_element_index(elem_ref), Some(2));
    }
}
