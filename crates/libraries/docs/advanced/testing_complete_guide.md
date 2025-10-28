# 测试完整指南

**Crate:** c11_libraries  
**主题:** Testing Complete Guide  
**Rust 版本:** 1.90.0  
**最后更新:** 2025年10月28日

---

## 📋 目录

- [测试完整指南](#测试完整指南)
  - [📋 目录](#-目录)
  - [🎯 测试概述](#-测试概述)
    - [测试金字塔](#测试金字塔)
    - [测试类型](#测试类型)
  - [✅ 单元测试](#-单元测试)
    - [基本单元测试](#1-基本单元测试)
    - [异步测试](#2-异步测试)
    - [错误处理测试](#3-错误处理测试)
  - [🔗 集成测试](#-集成测试)
    - [HTTP API 集成测试](#1-http-api-集成测试)
    - [数据库集成测试](#2-数据库集成测试)
    - [端到端测试](#3-端到端测试)
  - [⚡ 性能测试](#-性能测试)
    - [Criterion 基准测试](#1-criterion-基准测试)
    - [异步性能测试](#2-异步性能测试)
    - [压力测试](#3-压力测试)
  - [🎭 模拟和桩](#-模拟和桩)
    - [使用 mockall](#1-使用-mockall)
    - [HTTP Mock Server](#2-http-mock-server)
  - [🔍 属性测试](#-属性测试)
    - [QuickCheck](#1-quickcheck)
    - [Proptest](#2-proptest)
  - [📊 测试覆盖率](#-测试覆盖率)
    - [使用 tarpaulin](#1-使用-tarpaulin)
    - [覆盖率目标](#2-覆盖率目标)
    - [覆盖率报告](#3-覆盖率报告)
  - [🔄 测试驱动开发](#-测试驱动开发)
    - [TDD 周期](#tdd-周期)
    - [TDD 示例](#tdd-示例)
    - [TDD 最佳实践](#tdd-最佳实践)
  - [📚 总结](#-总结)
    - [测试清单](#测试清单)
    - [最佳实践](#最佳实践)

---

## 🎯 测试概述

### 测试金字塔

```
        /\
       /  \  E2E Tests (10%)
      /────\
     /      \  Integration Tests (20%)
    /────────\
   /          \  Unit Tests (70%)
  /────────────\
```

### 测试类型

```rust
// 1. 单元测试 (Unit Tests)
#[test]
fn test_add() {
    assert_eq!(add(2, 3), 5);
}

// 2. 集成测试 (Integration Tests)
#[tokio::test]
async fn test_api_endpoint() {
    let response = call_api("/users").await;
    assert_eq!(response.status(), 200);
}

// 3. 性能测试 (Benchmark Tests)
#[bench]
fn bench_sort(b: &mut Bencher) {
    b.iter(|| sort_data(&data));
}

// 4. 属性测试 (Property Tests)
#[quickcheck]
fn prop_reverse_reverse(xs: Vec<i32>) -> bool {
    let reversed = xs.iter().rev().copied().collect::<Vec<_>>();
    let double_reversed = reversed.iter().rev().copied().collect::<Vec<_>>();
    xs == double_reversed
}
```

---

## ✅ 单元测试

### 1. 基本单元测试

#### 测试函数

```rust
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_add_positive_numbers() {
        assert_eq!(add(2, 3), 5);
    }
    
    #[test]
    fn test_add_negative_numbers() {
        assert_eq!(add(-2, -3), -5);
    }
    
    #[test]
    fn test_add_zero() {
        assert_eq!(add(0, 5), 5);
        assert_eq!(add(5, 0), 5);
    }
    
    #[test]
    #[should_panic(expected = "overflow")]
    fn test_add_overflow() {
        add(i32::MAX, 1);
    }
}
```

---

#### 测试结构体方法

```rust
pub struct Calculator {
    memory: f64,
}

impl Calculator {
    pub fn new() -> Self {
        Self { memory: 0.0 }
    }
    
    pub fn add(&mut self, value: f64) {
        self.memory += value;
    }
    
    pub fn subtract(&mut self, value: f64) {
        self.memory -= value;
    }
    
    pub fn result(&self) -> f64 {
        self.memory
    }
    
    pub fn clear(&mut self) {
        self.memory = 0.0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_calculator_add() {
        let mut calc = Calculator::new();
        calc.add(5.0);
        assert_eq!(calc.result(), 5.0);
    }
    
    #[test]
    fn test_calculator_chain_operations() {
        let mut calc = Calculator::new();
        calc.add(10.0);
        calc.subtract(3.0);
        calc.add(2.0);
        assert_eq!(calc.result(), 9.0);
    }
    
    #[test]
    fn test_calculator_clear() {
        let mut calc = Calculator::new();
        calc.add(5.0);
        calc.clear();
        assert_eq!(calc.result(), 0.0);
    }
}
```

---

### 2. 异步测试

```rust
use tokio::test;

pub async fn fetch_user(id: u64) -> Result<User, Error> {
    // 异步获取用户
    let user = database::get_user(id).await?;
    Ok(user)
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_fetch_user_success() {
        let user = fetch_user(1).await.unwrap();
        assert_eq!(user.id, 1);
    }
    
    #[tokio::test]
    async fn test_fetch_user_not_found() {
        let result = fetch_user(999).await;
        assert!(result.is_err());
    }
    
    #[tokio::test]
    async fn test_concurrent_requests() {
        let futures = vec![
            fetch_user(1),
            fetch_user(2),
            fetch_user(3),
        ];
        
        let results = futures::future::join_all(futures).await;
        assert_eq!(results.len(), 3);
        assert!(results.iter().all(|r| r.is_ok()));
    }
}
```

---

### 3. 错误处理测试

```rust
#[derive(Debug, PartialEq)]
pub enum MathError {
    DivisionByZero,
    NegativeSquareRoot,
}

pub fn divide(a: f64, b: f64) -> Result<f64, MathError> {
    if b == 0.0 {
        Err(MathError::DivisionByZero)
    } else {
        Ok(a / b)
    }
}

pub fn sqrt(x: f64) -> Result<f64, MathError> {
    if x < 0.0 {
        Err(MathError::NegativeSquareRoot)
    } else {
        Ok(x.sqrt())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_divide_success() {
        assert_eq!(divide(10.0, 2.0).unwrap(), 5.0);
    }
    
    #[test]
    fn test_divide_by_zero() {
        assert_eq!(divide(10.0, 0.0), Err(MathError::DivisionByZero));
    }
    
    #[test]
    fn test_sqrt_positive() {
        assert_eq!(sqrt(4.0).unwrap(), 2.0);
    }
    
    #[test]
    fn test_sqrt_negative() {
        assert_eq!(sqrt(-1.0), Err(MathError::NegativeSquareRoot));
    }
    
    #[test]
    fn test_error_propagation() {
        let result = sqrt(-4.0)
            .and_then(|x| divide(10.0, x));
        
        assert_eq!(result, Err(MathError::NegativeSquareRoot));
    }
}
```

---

## 🔗 集成测试

### 1. HTTP API 集成测试

```rust
// tests/api_tests.rs
use axum::{Router, routing::get, http::StatusCode};
use tower::ServiceExt;

async fn create_app() -> Router {
    Router::new()
        .route("/health", get(health_check))
        .route("/users/:id", get(get_user))
}

async fn health_check() -> StatusCode {
    StatusCode::OK
}

async fn get_user(Path(id): Path<u64>) -> Result<Json<User>, StatusCode> {
    // 实现获取用户逻辑
    todo!()
}

#[tokio::test]
async fn test_health_check() {
    let app = create_app().await;
    
    let response = app
        .oneshot(
            Request::builder()
                .uri("/health")
                .body(Body::empty())
                .unwrap()
        )
        .await
        .unwrap();
    
    assert_eq!(response.status(), StatusCode::OK);
}

#[tokio::test]
async fn test_get_user() {
    let app = create_app().await;
    
    let response = app
        .oneshot(
            Request::builder()
                .uri("/users/1")
                .body(Body::empty())
                .unwrap()
        )
        .await
        .unwrap();
    
    assert_eq!(response.status(), StatusCode::OK);
    
    let body = hyper::body::to_bytes(response.into_body()).await.unwrap();
    let user: User = serde_json::from_slice(&body).unwrap();
    
    assert_eq!(user.id, 1);
}
```

---

### 2. 数据库集成测试

```rust
use sqlx::PgPool;

async fn setup_test_db() -> PgPool {
    let database_url = std::env::var("TEST_DATABASE_URL")
        .expect("TEST_DATABASE_URL must be set");
    
    let pool = PgPool::connect(&database_url).await.unwrap();
    
    // 运行迁移
    sqlx::migrate!("./migrations")
        .run(&pool)
        .await
        .unwrap();
    
    pool
}

async fn cleanup_test_db(pool: &PgPool) {
    sqlx::query("DELETE FROM users").execute(pool).await.unwrap();
}

#[tokio::test]
async fn test_create_user() {
    let pool = setup_test_db().await;
    
    // 插入用户
    let user = User {
        id: 0,
        email: "test@example.com".to_string(),
        name: "Test User".to_string(),
    };
    
    let created = create_user(&pool, user).await.unwrap();
    
    // 验证
    assert!(created.id > 0);
    assert_eq!(created.email, "test@example.com");
    
    // 清理
    cleanup_test_db(&pool).await;
}

#[tokio::test]
async fn test_find_user_by_email() {
    let pool = setup_test_db().await;
    
    // 准备数据
    let user = create_user(&pool, User {
        id: 0,
        email: "find@example.com".to_string(),
        name: "Find Me".to_string(),
    }).await.unwrap();
    
    // 查询
    let found = find_user_by_email(&pool, "find@example.com").await.unwrap();
    
    assert_eq!(found.id, user.id);
    assert_eq!(found.email, "find@example.com");
    
    cleanup_test_db(&pool).await;
}
```

---

### 3. 端到端测试

```rust
use reqwest::Client;

#[tokio::test]
async fn test_e2e_user_registration_flow() {
    // 启动测试服务器
    let server = spawn_test_server().await;
    let client = Client::new();
    let base_url = server.url();
    
    // 1. 注册用户
    let register_payload = json!({
        "email": "newuser@example.com",
        "password": "SecurePass123",
        "name": "New User"
    });
    
    let register_response = client
        .post(format!("{}/register", base_url))
        .json(&register_payload)
        .send()
        .await
        .unwrap();
    
    assert_eq!(register_response.status(), 201);
    let user: User = register_response.json().await.unwrap();
    
    // 2. 登录
    let login_payload = json!({
        "email": "newuser@example.com",
        "password": "SecurePass123"
    });
    
    let login_response = client
        .post(format!("{}/login", base_url))
        .json(&login_payload)
        .send()
        .await
        .unwrap();
    
    assert_eq!(login_response.status(), 200);
    let token: String = login_response.json::<LoginResponse>().await.unwrap().token;
    
    // 3. 使用 token 访问受保护资源
    let profile_response = client
        .get(format!("{}/profile", base_url))
        .bearer_auth(&token)
        .send()
        .await
        .unwrap();
    
    assert_eq!(profile_response.status(), 200);
    let profile: User = profile_response.json().await.unwrap();
    assert_eq!(profile.email, "newuser@example.com");
    
    // 清理
    server.shutdown().await;
}
```

---

## ⚡ 性能测试

### 1. Criterion 基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};

fn fibonacci_recursive(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        n => fibonacci_recursive(n - 1) + fibonacci_recursive(n - 2),
    }
}

fn fibonacci_iterative(n: u64) -> u64 {
    let mut a = 0;
    let mut b = 1;
    for _ in 0..n {
        let temp = a;
        a = b;
        b = temp + b;
    }
    a
}

fn benchmark_fibonacci(c: &mut Criterion) {
    let mut group = c.benchmark_group("fibonacci");
    
    for n in [10, 15, 20].iter() {
        group.bench_with_input(BenchmarkId::new("recursive", n), n, |b, &n| {
            b.iter(|| fibonacci_recursive(black_box(n)))
        });
        
        group.bench_with_input(BenchmarkId::new("iterative", n), n, |b, &n| {
            b.iter(|| fibonacci_iterative(black_box(n)))
        });
    }
    
    group.finish();
}

criterion_group!(benches, benchmark_fibonacci);
criterion_main!(benches);
```

---

### 2. 异步性能测试

```rust
use criterion::{criterion_group, criterion_main, Criterion};
use tokio::runtime::Runtime;

fn benchmark_async_operations(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    c.bench_function("fetch_user", |b| {
        b.to_async(&rt).iter(|| async {
            fetch_user(1).await.unwrap()
        });
    });
    
    c.bench_function("concurrent_fetch", |b| {
        b.to_async(&rt).iter(|| async {
            let futures = (1..=10).map(|i| fetch_user(i));
            futures::future::join_all(futures).await
        });
    });
}

criterion_group!(benches, benchmark_async_operations);
criterion_main!(benches);
```

---

### 3. 压力测试

```rust
#[tokio::test]
async fn test_load_stress() {
    let app = create_app().await;
    let concurrent_requests = 1000;
    let mut tasks = Vec::new();
    
    for i in 0..concurrent_requests {
        let app_clone = app.clone();
        let task = tokio::spawn(async move {
            let response = app_clone
                .oneshot(
                    Request::builder()
                        .uri(format!("/users/{}", i % 100))
                        .body(Body::empty())
                        .unwrap()
                )
                .await
                .unwrap();
            
            response.status()
        });
        
        tasks.push(task);
    }
    
    let results = futures::future::join_all(tasks).await;
    let success_count = results.iter()
        .filter(|r| r.as_ref().unwrap() == &StatusCode::OK)
        .count();
    
    // 至少 95% 成功率
    assert!(success_count as f64 / concurrent_requests as f64 >= 0.95);
}
```

---

## 🎭 模拟和桩

### 1. 使用 mockall

```rust
use mockall::*;
use async_trait::async_trait;

#[automock]
#[async_trait]
pub trait UserRepository {
    async fn find_by_id(&self, id: u64) -> Result<User, Error>;
    async fn create(&self, user: User) -> Result<User, Error>;
    async fn delete(&self, id: u64) -> Result<(), Error>;
}

pub struct UserService<R: UserRepository> {
    repo: R,
}

impl<R: UserRepository> UserService<R> {
    pub fn new(repo: R) -> Self {
        Self { repo }
    }
    
    pub async fn get_user(&self, id: u64) -> Result<User, Error> {
        self.repo.find_by_id(id).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_get_user_success() {
        let mut mock_repo = MockUserRepository::new();
        
        // 设置期望
        mock_repo
            .expect_find_by_id()
            .with(eq(1))
            .times(1)
            .returning(|id| {
                Ok(User {
                    id,
                    email: "test@example.com".to_string(),
                    name: "Test User".to_string(),
                })
            });
        
        let service = UserService::new(mock_repo);
        let user = service.get_user(1).await.unwrap();
        
        assert_eq!(user.id, 1);
        assert_eq!(user.email, "test@example.com");
    }
    
    #[tokio::test]
    async fn test_get_user_not_found() {
        let mut mock_repo = MockUserRepository::new();
        
        mock_repo
            .expect_find_by_id()
            .with(eq(999))
            .times(1)
            .returning(|_| Err(Error::NotFound));
        
        let service = UserService::new(mock_repo);
        let result = service.get_user(999).await;
        
        assert!(result.is_err());
    }
}
```

---

### 2. HTTP Mock Server

```rust
use wiremock::{MockServer, Mock, ResponseTemplate};
use wiremock::matchers::{method, path};

#[tokio::test]
async fn test_external_api_call() {
    // 启动 mock server
    let mock_server = MockServer::start().await;
    
    // 配置 mock 响应
    Mock::given(method("GET"))
        .and(path("/users/1"))
        .respond_with(ResponseTemplate::new(200).set_body_json(json!({
            "id": 1,
            "name": "John Doe",
            "email": "john@example.com"
        })))
        .mount(&mock_server)
        .await;
    
    // 测试代码
    let client = Client::new();
    let response = client
        .get(format!("{}/users/1", mock_server.uri()))
        .send()
        .await
        .unwrap();
    
    assert_eq!(response.status(), 200);
    let user: User = response.json().await.unwrap();
    assert_eq!(user.name, "John Doe");
}
```

---

## 属性测试

### 1. QuickCheck

```rust
use quickcheck::{quickcheck, TestResult};
use quickcheck_macros::quickcheck;

// 属性：逆转两次应该得到原始值
#[quickcheck]
fn prop_reverse_reverse(xs: Vec<i32>) -> bool {
    let reversed: Vec<i32> = xs.iter().rev().copied().collect();
    let double_reversed: Vec<i32> = reversed.iter().rev().copied().collect();
    xs == double_reversed
}

// 属性：排序后的列表应该是有序的
#[quickcheck]
fn prop_sort_is_sorted(mut xs: Vec<i32>) -> bool {
    xs.sort();
    xs.windows(2).all(|w| w[0] <= w[1])
}

// 属性：map 后的长度应该相同
#[quickcheck]
fn prop_map_preserves_length(xs: Vec<i32>) -> bool {
    let mapped: Vec<i32> = xs.iter().map(|&x| x * 2).collect();
    xs.len() == mapped.len()
}

// 条件属性测试
#[quickcheck]
fn prop_divide_multiply(a: i32, b: i32) -> TestResult {
    if b == 0 {
        return TestResult::discard();  // 跳过这个测试用例
    }
    
    TestResult::from_bool((a / b) * b + (a % b) == a)
}
```

---

### 2. Proptest

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_string_length(s in ".*") {
        assert_eq!(s.len(), s.chars().count());
    }
    
    #[test]
    fn test_vec_push_pop(
        mut v in prop::collection::vec(any::<i32>(), 0..100),
        x in any::<i32>()
    ) {
        v.push(x);
        assert_eq!(v.pop(), Some(x));
    }
    
    #[test]
    fn test_addition_commutative(a in 0..1000i32, b in 0..1000i32) {
        assert_eq!(a + b, b + a);
    }
}

// 自定义策略
fn user_strategy() -> impl Strategy<Value = User> {
    (any::<u64>(), "[a-z]{5,10}@example\\.com", "[A-Za-z ]{3,20}")
        .prop_map(|(id, email, name)| User { id, email, name })
}

proptest! {
    #[test]
    fn test_user_email_valid(user in user_strategy()) {
        assert!(user.email.contains('@'));
        assert!(user.email.ends_with(".com"));
    }
}
```

---

## 测试覆盖率

### 1. 使用 tarpaulin

```bash
# 安装
cargo install cargo-tarpaulin

# 运行覆盖率分析
cargo tarpaulin --out Html --output-dir coverage

# 只测试特定包
cargo tarpaulin --workspace --exclude-files "target/*" --out Lcov
```

```toml
# Cargo.toml
[package.metadata.tarpaulin]
exclude-files = [
    "tests/*",
    "benches/*",
]
```

---

### 2. 覆盖率目标

```rust
// 设置覆盖率目标
#![cfg_attr(coverage, feature(coverage_attribute))]

#[cfg_attr(coverage, coverage(off))]
fn generated_code() {
    // 生成的代码，不计入覆盖率
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_critical_path() {
        // 确保关键路径有测试覆盖
    }
}
```

---

### 3. 覆盖率报告

```rust
// 在 CI/CD 中集成覆盖率检查
// .github/workflows/test.yml

- name: Run tests with coverage
  run: |
    cargo tarpaulin --out Xml --output-dir coverage
    
- name: Upload coverage to Codecov
  uses: codecov/codecov-action@v3
  with:
    files: coverage/cobertura.xml
    
- name: Check coverage threshold
  run: |
    COVERAGE=$(cargo tarpaulin --print-json | jq '.coverage')
    if (( $(echo "$COVERAGE < 80" | bc -l) )); then
      echo "Coverage $COVERAGE% is below 80%"
      exit 1
    fi
```

---

## 测试驱动开发

### TDD 周期

```
┌─────────────────────────────────────┐
│          TDD Red-Green-Refactor     │
├─────────────────────────────────────┤
│ 1. Red:   写一个失败的测试           │
│ 2. Green: 写最少的代码使测试通过      │
│ 3. Refactor: 重构代码改进设计        │
└─────────────────────────────────────┘
```

### TDD 示例

```rust
// Step 1: Red - 写失败的测试
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_calculate_discount() {
        let price = 100.0;
        let discount = calculate_discount(price, 10.0);
        assert_eq!(discount, 90.0);
    }
}

// Step 2: Green - 最简实现
pub fn calculate_discount(price: f64, percentage: f64) -> f64 {
    price - (price * percentage / 100.0)
}

// Step 3: Refactor - 添加更多测试和改进
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_calculate_discount_zero() {
        assert_eq!(calculate_discount(100.0, 0.0), 100.0);
    }
    
    #[test]
    fn test_calculate_discount_full() {
        assert_eq!(calculate_discount(100.0, 100.0), 0.0);
    }
    
    #[test]
    #[should_panic]
    fn test_calculate_discount_negative_percentage() {
        calculate_discount(100.0, -10.0);
    }
}

// Refactored implementation
pub fn calculate_discount(price: f64, percentage: f64) -> f64 {
    assert!(percentage >= 0.0 && percentage <= 100.0, "Invalid percentage");
    price * (1.0 - percentage / 100.0)
}
```

---

### TDD 最佳实践

```rust
// 1. 测试先行
#[test]
fn test_user_authentication() {
    let user = User::new("test@example.com", "password123");
    assert!(user.authenticate("password123"));
    assert!(!user.authenticate("wrongpassword"));
}

// 2. 一次只关注一个功能
#[test]
fn test_email_validation_valid() {
    assert!(validate_email("test@example.com"));
}

#[test]
fn test_email_validation_invalid() {
    assert!(!validate_email("invalid-email"));
}

// 3. 测试边界条件
#[test]
fn test_boundary_conditions() {
    assert_eq!(process_age(0), "infant");
    assert_eq!(process_age(17), "minor");
    assert_eq!(process_age(18), "adult");
    assert_eq!(process_age(120), "elderly");
}

// 4. 使用描述性测试名称
#[test]
fn given_empty_cart_when_add_item_then_cart_has_one_item() {
    let mut cart = ShoppingCart::new();
    cart.add_item(Item::new("Product", 10.0));
    assert_eq!(cart.item_count(), 1);
}
```

---

## 总结

### 测试清单

- ✅ **单元测试**: 函数、方法、错误处理
- ✅ **集成测试**: API、数据库、E2E
- ✅ **性能测试**: Criterion、压力测试
- ✅ **Mock/Stub**: mockall、wiremock
- ✅ **属性测试**: QuickCheck、Proptest
- ✅ **覆盖率**: tarpaulin、CI/CD 集成
- ✅ **TDD**: Red-Green-Refactor 周期

### 最佳实践

1. **测试金字塔**: 70% 单元，20% 集成，10% E2E
2. **快速反馈**: 单元测试要快
3. **独立性**: 测试间不相互依赖
4. **可重复**: 每次运行结果一致
5. **清晰明确**: 测试名称描述性强
6. **覆盖率目标**: 至少 80% 代码覆盖

---

**文档贡献者:** AI Assistant  
**审核状态:** ✅ 已完成  
**最后更新:** 2025年10月28日

