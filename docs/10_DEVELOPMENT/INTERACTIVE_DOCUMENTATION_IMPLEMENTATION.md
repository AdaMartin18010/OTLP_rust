# 交互式文档实现方案

**版本**: 1.0
**日期**: 2025年10月26日
**项目**: OTLP 交互式文档系统
**状态**: 🚀 开发中

> **简介**: 交互式文档系统 - 可执行代码、实时编译、交互式教程和可视化演示。

---

## 📋 项目概述

本文档详细描述了 OTLP Rust 项目交互式文档系统的实现方案，包括可执行代码示例、实时编译、交互式教程和可视化演示等功能。

### 核心特性

- 🎮 **可执行代码**: 在线 Rust 代码编辑和运行
- 🔄 **实时编译**: 即时编译反馈和错误提示
- 📚 **交互式教程**: 分步骤的学习体验
- 📊 **可视化演示**: 动态图表和数据展示
- 🎯 **个性化学习**: 自适应学习路径

---

## 🛠️ 技术架构

### 1. 前端架构

#### 1.1 技术栈选择

```typescript
// 前端技术栈
const FrontendStack = {
  framework: "Next.js 14",
  language: "TypeScript",
  styling: "Tailwind CSS + Styled Components",
  state: "Zustand + React Query",
  editor: "Monaco Editor",
  charts: "D3.js + Recharts",
  animations: "Framer Motion",
  testing: "Jest + Testing Library"
}
```

#### 1.2 组件架构

```typescript
// 核心组件结构
interface InteractiveDocComponents {
  CodeEditor: {
    language: 'rust';
    theme: 'vs-dark' | 'vs-light';
    features: ['intellisense', 'debugging', 'formatting'];
  };

  TutorialPlayer: {
    steps: TutorialStep[];
    progress: number;
    autoAdvance: boolean;
  };

  Visualization: {
    type: 'chart' | 'diagram' | 'animation';
    data: any;
    interactive: boolean;
  };

  CompilerOutput: {
    status: 'success' | 'error' | 'warning';
    output: string;
    errors: CompilerError[];
  };
}
```

### 2. 后端服务

#### 2.1 编译服务

```rust
// Rust 编译服务
use axum::{Router, routing::post, Json};
use serde::{Deserialize, Serialize};

#[derive(Deserialize)]
struct CompileRequest {
    code: String,
    edition: String,
    features: Vec<String>,
}

#[derive(Serialize)]
struct CompileResponse {
    success: bool,
    output: String,
    errors: Vec<CompilerError>,
    warnings: Vec<CompilerWarning>,
}

pub async fn compile_rust_code(
    Json(request): Json<CompileRequest>
) -> Result<Json<CompileResponse>, AppError> {
    let result = rustc_compile(&request.code, &request.edition, &request.features).await?;

    Ok(Json(CompileResponse {
        success: result.success,
        output: result.stdout,
        errors: result.errors,
        warnings: result.warnings,
    }))
}
```

#### 2.2 代码执行服务

```rust
// 代码执行服务
use tokio::process::Command;
use std::time::Duration;

pub struct CodeExecutor {
    timeout: Duration,
    memory_limit: usize,
    sandbox: bool,
}

impl CodeExecutor {
    pub async fn execute_rust_code(&self, code: &str) -> Result<ExecutionResult, Error> {
        // 创建临时文件
        let temp_file = self.create_temp_file(code).await?;

        // 编译代码
        let compile_result = self.compile_code(&temp_file).await?;
        if !compile_result.success {
            return Ok(ExecutionResult::CompileError(compile_result.errors));
        }

        // 执行代码
        let execution_result = self.run_code(&temp_file).await?;

        // 清理临时文件
        self.cleanup_temp_file(&temp_file).await?;

        Ok(execution_result)
    }

    async fn run_code(&self, file_path: &Path) -> Result<ExecutionResult, Error> {
        let output = Command::new("timeout")
            .arg(self.timeout.as_secs().to_string())
            .arg("./target/debug/example")
            .current_dir(file_path.parent().unwrap())
            .output()
            .await?;

        Ok(ExecutionResult::Success {
            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
            exit_code: output.status.code(),
        })
    }
}
```

### 3. 数据库设计

#### 3.1 教程数据模型

```sql
-- 教程表
CREATE TABLE tutorials (
    id UUID PRIMARY KEY,
    title VARCHAR(255) NOT NULL,
    description TEXT,
    difficulty_level INTEGER CHECK (difficulty_level BETWEEN 1 AND 5),
    estimated_duration INTEGER, -- 分钟
    prerequisites TEXT[],
    learning_objectives TEXT[],
    created_at TIMESTAMP DEFAULT NOW(),
    updated_at TIMESTAMP DEFAULT NOW()
);

-- 教程步骤表
CREATE TABLE tutorial_steps (
    id UUID PRIMARY KEY,
    tutorial_id UUID REFERENCES tutorials(id),
    step_number INTEGER NOT NULL,
    title VARCHAR(255) NOT NULL,
    content TEXT NOT NULL,
    code_example TEXT,
    expected_output TEXT,
    hints TEXT[],
    solution TEXT,
    created_at TIMESTAMP DEFAULT NOW()
);

-- 用户进度表
CREATE TABLE user_progress (
    id UUID PRIMARY KEY,
    user_id UUID,
    tutorial_id UUID REFERENCES tutorials(id),
    current_step INTEGER DEFAULT 1,
    completed_steps INTEGER[],
    started_at TIMESTAMP DEFAULT NOW(),
    completed_at TIMESTAMP,
    time_spent INTEGER DEFAULT 0 -- 秒
);
```

#### 3.2 代码示例数据模型

```sql
-- 代码示例表
CREATE TABLE code_examples (
    id UUID PRIMARY KEY,
    title VARCHAR(255) NOT NULL,
    description TEXT,
    code TEXT NOT NULL,
    language VARCHAR(50) DEFAULT 'rust',
    category VARCHAR(100),
    tags TEXT[],
    difficulty_level INTEGER,
    runnable BOOLEAN DEFAULT true,
    created_at TIMESTAMP DEFAULT NOW()
);

-- 执行历史表
CREATE TABLE execution_history (
    id UUID PRIMARY KEY,
    user_id UUID,
    example_id UUID REFERENCES code_examples(id),
    code TEXT NOT NULL,
    output TEXT,
    success BOOLEAN,
    execution_time INTEGER, -- 毫秒
    created_at TIMESTAMP DEFAULT NOW()
);
```

---

## 🎮 交互功能实现

### 1. 可执行代码编辑器

#### 1.1 Monaco Editor 集成

```typescript
// 代码编辑器组件
import { Editor } from '@monaco-editor/react';
import { useCallback, useState } from 'react';

interface CodeEditorProps {
  initialCode: string;
  onCodeChange: (code: string) => void;
  onRun: (code: string) => void;
  language?: string;
  theme?: string;
}

export const CodeEditor: React.FC<CodeEditorProps> = ({
  initialCode,
  onCodeChange,
  onRun,
  language = 'rust',
  theme = 'vs-dark'
}) => {
  const [code, setCode] = useState(initialCode);
  const [isRunning, setIsRunning] = useState(false);
  const [output, setOutput] = useState<string>('');

  const handleEditorChange = useCallback((value: string | undefined) => {
    const newCode = value || '';
    setCode(newCode);
    onCodeChange(newCode);
  }, [onCodeChange]);

  const handleRun = useCallback(async () => {
    setIsRunning(true);
    try {
      const result = await fetch('/api/compile', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ code, language: 'rust' })
      });

      const data = await result.json();
      setOutput(data.output);

      if (data.success) {
        onRun(code);
      }
    } catch (error) {
      setOutput(`Error: ${error.message}`);
    } finally {
      setIsRunning(false);
    }
  }, [code, onRun]);

  return (
    <div className="code-editor-container">
      <div className="editor-toolbar">
        <button
          onClick={handleRun}
          disabled={isRunning}
          className="run-button"
        >
          {isRunning ? 'Running...' : 'Run Code'}
        </button>
      </div>

      <Editor
        height="400px"
        language={language}
        theme={theme}
        value={code}
        onChange={handleEditorChange}
        options={{
          minimap: { enabled: false },
          fontSize: 14,
          lineNumbers: 'on',
          roundedSelection: false,
          scrollBeyondLastLine: false,
          automaticLayout: true,
        }}
      />

      {output && (
        <div className="output-panel">
          <h3>Output:</h3>
          <pre>{output}</pre>
        </div>
      )}
    </div>
  );
};
```

#### 1.2 实时编译反馈

```typescript
// 实时编译服务
class RealtimeCompiler {
  private debounceTimer: NodeJS.Timeout | null = null;
  private lastCode: string = '';

  constructor(
    private onCompileResult: (result: CompileResult) => void,
    private debounceMs: number = 1000
  ) {}

  async compileCode(code: string): Promise<void> {
    if (this.debounceTimer) {
      clearTimeout(this.debounceTimer);
    }

    this.debounceTimer = setTimeout(async () => {
      if (code === this.lastCode) return;

      this.lastCode = code;

      try {
        const response = await fetch('/api/compile', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ code, language: 'rust' })
        });

        const result = await response.json();
        this.onCompileResult(result);
      } catch (error) {
        this.onCompileResult({
          success: false,
          errors: [{ message: error.message, line: 0, column: 0 }],
          warnings: []
        });
      }
    }, this.debounceMs);
  }

  destroy(): void {
    if (this.debounceTimer) {
      clearTimeout(this.debounceTimer);
    }
  }
}
```

### 2. 交互式教程系统

#### 2.1 教程播放器

```typescript
// 教程播放器组件
interface TutorialStep {
  id: string;
  title: string;
  content: string;
  codeExample?: string;
  expectedOutput?: string;
  hints: string[];
  solution?: string;
}

interface TutorialPlayerProps {
  tutorial: Tutorial;
  onStepComplete: (stepId: string) => void;
  onTutorialComplete: () => void;
}

export const TutorialPlayer: React.FC<TutorialPlayerProps> = ({
  tutorial,
  onStepComplete,
  onTutorialComplete
}) => {
  const [currentStep, setCurrentStep] = useState(0);
  const [userCode, setUserCode] = useState('');
  const [showHint, setShowHint] = useState(false);
  const [showSolution, setShowSolution] = useState(false);

  const step = tutorial.steps[currentStep];
  const isLastStep = currentStep === tutorial.steps.length - 1;

  const handleNextStep = () => {
    onStepComplete(step.id);

    if (isLastStep) {
      onTutorialComplete();
    } else {
      setCurrentStep(prev => prev + 1);
      setUserCode('');
      setShowHint(false);
      setShowSolution(false);
    }
  };

  const handleCodeSubmit = async () => {
    if (!step.expectedOutput) {
      handleNextStep();
      return;
    }

    const result = await compileCode(userCode);
    if (result.success && result.output.includes(step.expectedOutput)) {
      handleNextStep();
    } else {
      // 显示错误或提示
    }
  };

  return (
    <div className="tutorial-player">
      <div className="progress-bar">
        <div
          className="progress-fill"
          style={{ width: `${((currentStep + 1) / tutorial.steps.length) * 100}%` }}
        />
      </div>

      <div className="step-content">
        <h2>{step.title}</h2>
        <div className="content" dangerouslySetInnerHTML={{ __html: step.content }} />

        {step.codeExample && (
          <CodeEditor
            initialCode={step.codeExample}
            onCodeChange={setUserCode}
            onRun={handleCodeSubmit}
          />
        )}

        <div className="step-actions">
          <button onClick={() => setShowHint(!showHint)}>
            {showHint ? 'Hide Hint' : 'Show Hint'}
          </button>

          {step.solution && (
            <button onClick={() => setShowSolution(!showSolution)}>
              {showSolution ? 'Hide Solution' : 'Show Solution'}
            </button>
          )}

          <button onClick={handleNextStep} className="next-button">
            {isLastStep ? 'Complete Tutorial' : 'Next Step'}
          </button>
        </div>

        {showHint && (
          <div className="hint-panel">
            <h3>Hint:</h3>
            <p>{step.hints[0]}</p>
          </div>
        )}

        {showSolution && step.solution && (
          <div className="solution-panel">
            <h3>Solution:</h3>
            <pre>{step.solution}</pre>
          </div>
        )}
      </div>
    </div>
  );
};
```

#### 2.2 进度追踪

```typescript
// 进度追踪服务
class ProgressTracker {
  private progress: Map<string, TutorialProgress> = new Map();

  async saveProgress(tutorialId: string, stepId: string, code: string): Promise<void> {
    const progress = this.progress.get(tutorialId) || {
      tutorialId,
      currentStep: 0,
      completedSteps: [],
      codeHistory: []
    };

    progress.codeHistory.push({
      stepId,
      code,
      timestamp: Date.now()
    });

    if (!progress.completedSteps.includes(stepId)) {
      progress.completedSteps.push(stepId);
    }

    this.progress.set(tutorialId, progress);

    // 保存到服务器
    await fetch('/api/progress', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(progress)
    });
  }

  getProgress(tutorialId: string): TutorialProgress | null {
    return this.progress.get(tutorialId) || null;
  }

  getCompletionRate(tutorialId: string): number {
    const progress = this.progress.get(tutorialId);
    if (!progress) return 0;

    // 从服务器获取教程总步数
    const totalSteps = this.getTutorialStepCount(tutorialId);
    return (progress.completedSteps.length / totalSteps) * 100;
  }
}
```

### 3. 可视化演示

#### 3.1 架构图交互

```typescript
// 交互式架构图组件
import { useEffect, useRef } from 'react';
import * as d3 from 'd3';

interface ArchitectureNode {
  id: string;
  name: string;
  type: 'service' | 'database' | 'queue' | 'cache';
  position: { x: number; y: number };
  connections: string[];
  description: string;
}

interface InteractiveArchitectureProps {
  nodes: ArchitectureNode[];
  onNodeClick: (node: ArchitectureNode) => void;
}

export const InteractiveArchitecture: React.FC<InteractiveArchitectureProps> = ({
  nodes,
  onNodeClick
}) => {
  const svgRef = useRef<SVGSVGElement>(null);

  useEffect(() => {
    if (!svgRef.current) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    const width = 800;
    const height = 600;

    // 创建节点
    const nodeElements = svg.selectAll('.node')
      .data(nodes)
      .enter()
      .append('g')
      .attr('class', 'node')
      .attr('transform', d => `translate(${d.position.x}, ${d.position.y})`)
      .style('cursor', 'pointer');

    // 添加节点背景
    nodeElements.append('rect')
      .attr('width', 120)
      .attr('height', 60)
      .attr('rx', 8)
      .attr('fill', d => getNodeColor(d.type))
      .attr('stroke', '#333')
      .attr('stroke-width', 2);

    // 添加节点文本
    nodeElements.append('text')
      .attr('x', 60)
      .attr('y', 35)
      .attr('text-anchor', 'middle')
      .attr('fill', 'white')
      .attr('font-size', '12px')
      .text(d => d.name);

    // 添加连接线
    nodes.forEach(node => {
      node.connections.forEach(connectionId => {
        const targetNode = nodes.find(n => n.id === connectionId);
        if (targetNode) {
          svg.append('line')
            .attr('x1', node.position.x + 60)
            .attr('y1', node.position.y + 30)
            .attr('x2', targetNode.position.x + 60)
            .attr('y2', targetNode.position.y + 30)
            .attr('stroke', '#666')
            .attr('stroke-width', 2)
            .attr('marker-end', 'url(#arrowhead)');
        }
      });
    });

    // 添加箭头标记
    svg.append('defs').append('marker')
      .attr('id', 'arrowhead')
      .attr('viewBox', '0 0 10 10')
      .attr('refX', 8)
      .attr('refY', 3)
      .attr('markerWidth', 6)
      .attr('markerHeight', 6)
      .attr('orient', 'auto')
      .append('path')
      .attr('d', 'M0,0 L0,6 L9,3 z')
      .attr('fill', '#666');

    // 添加点击事件
    nodeElements.on('click', (event, d) => {
      onNodeClick(d);
    });

    // 添加悬停效果
    nodeElements.on('mouseover', function(event, d) {
      d3.select(this).select('rect')
        .attr('stroke', '#007acc')
        .attr('stroke-width', 3);
    })
    .on('mouseout', function(event, d) {
      d3.select(this).select('rect')
        .attr('stroke', '#333')
        .attr('stroke-width', 2);
    });

  }, [nodes, onNodeClick]);

  const getNodeColor = (type: string): string => {
    const colors = {
      service: '#4CAF50',
      database: '#2196F3',
      queue: '#FF9800',
      cache: '#9C27B0'
    };
    return colors[type as keyof typeof colors] || '#666';
  };

  return (
    <div className="interactive-architecture">
      <svg ref={svgRef} width={800} height={600} />
    </div>
  );
};
```

#### 3.2 数据流动画

```typescript
// 数据流动画组件
interface DataFlowAnimationProps {
  data: any[];
  flowPath: string[];
  duration?: number;
}

export const DataFlowAnimation: React.FC<DataFlowAnimationProps> = ({
  data,
  flowPath,
  duration = 2000
}) => {
  const [currentStep, setCurrentStep] = useState(0);
  const [isAnimating, setIsAnimating] = useState(false);

  const startAnimation = useCallback(() => {
    setIsAnimating(true);
    setCurrentStep(0);

    const interval = setInterval(() => {
      setCurrentStep(prev => {
        if (prev >= flowPath.length - 1) {
          clearInterval(interval);
          setIsAnimating(false);
          return prev;
        }
        return prev + 1;
      });
    }, duration / flowPath.length);

    return () => clearInterval(interval);
  }, [flowPath, duration]);

  return (
    <div className="data-flow-animation">
      <div className="flow-controls">
        <button onClick={startAnimation} disabled={isAnimating}>
          {isAnimating ? 'Animating...' : 'Start Animation'}
        </button>
      </div>

      <div className="flow-diagram">
        {flowPath.map((step, index) => (
          <div
            key={step}
            className={`flow-step ${index === currentStep ? 'active' : ''} ${index < currentStep ? 'completed' : ''}`}
          >
            <div className="step-icon">
              {index < currentStep ? '✓' : index === currentStep ? '→' : '○'}
            </div>
            <div className="step-label">{step}</div>
            {index === currentStep && (
              <div className="data-preview">
                <pre>{JSON.stringify(data[index], null, 2)}</pre>
              </div>
            )}
          </div>
        ))}
      </div>
    </div>
  );
};
```

---

## 🚀 部署和运维

### 1. 容器化部署

#### 1.1 Docker 配置

```dockerfile
# 前端 Dockerfile
FROM node:18-alpine AS builder

WORKDIR /app
COPY package*.json ./
RUN npm ci --only=production

COPY . .
RUN npm run build

FROM nginx:alpine
COPY --from=builder /app/out /usr/share/nginx/html
COPY nginx.conf /etc/nginx/nginx.conf

EXPOSE 80
CMD ["nginx", "-g", "daemon off;"]
```

```dockerfile
# 后端 Dockerfile
FROM rust:1.90-alpine AS builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
RUN cargo fetch

COPY src ./src
RUN cargo build --release

FROM alpine:latest
RUN apk --no-cache add ca-certificates
WORKDIR /root/

COPY --from=builder /app/target/release/docs-api ./
EXPOSE 8000
CMD ["./docs-api"]
```

#### 1.2 Docker Compose

```yaml
version: '3.8'

services:
  docs-frontend:
    build: ./frontend
    ports:
      - "3000:80"
    depends_on:
      - docs-api
    environment:
      - NEXT_PUBLIC_API_URL=http://localhost:8000

  docs-api:
    build: ./backend
    ports:
      - "8000:8000"
    environment:
      - DATABASE_URL=postgresql://user:pass@db:5432/docs
      - REDIS_URL=redis://redis:6379
      - RUST_LOG=info
    depends_on:
      - db
      - redis

  db:
    image: postgres:15
    environment:
      - POSTGRES_DB=docs
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=pass
    volumes:
      - postgres_data:/var/lib/postgresql/data

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"

volumes:
  postgres_data:
```

### 2. 监控和日志

#### 2.1 应用监控

```rust
// 监控中间件
use axum::{middleware, Router};
use tower::ServiceBuilder;
use tower_http::trace::TraceLayer;

pub fn create_app() -> Router {
    Router::new()
        .route("/api/compile", post(compile_rust_code))
        .route("/api/execute", post(execute_code))
        .route("/api/tutorials", get(get_tutorials))
        .layer(
            ServiceBuilder::new()
                .layer(TraceLayer::new_for_http())
                .layer(middleware::from_fn(logging_middleware))
                .layer(middleware::from_fn(metrics_middleware))
        )
}

async fn logging_middleware(
    request: Request<Body>,
    next: Next<Body>,
) -> Result<Response, StatusCode> {
    let start = std::time::Instant::now();
    let method = request.method().clone();
    let uri = request.uri().clone();

    let response = next.run(request).await;

    let duration = start.elapsed();
    tracing::info!(
        method = %method,
        uri = %uri,
        status = %response.status(),
        duration_ms = duration.as_millis(),
        "Request completed"
    );

    Ok(response)
}
```

#### 2.2 性能监控

```typescript
// 前端性能监控
class PerformanceMonitor {
  private metrics: Map<string, number[]> = new Map();

  startTiming(operation: string): () => void {
    const start = performance.now();

    return () => {
      const duration = performance.now() - start;
      this.recordMetric(operation, duration);
    };
  }

  recordMetric(operation: string, value: number): void {
    const metrics = this.metrics.get(operation) || [];
    metrics.push(value);
    this.metrics.set(operation, metrics);

    // 发送到分析服务
    this.sendMetrics(operation, value);
  }

  private async sendMetrics(operation: string, value: number): Promise<void> {
    try {
      await fetch('/api/metrics', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          operation,
          value,
          timestamp: Date.now(),
          userAgent: navigator.userAgent
        })
      });
    } catch (error) {
      console.error('Failed to send metrics:', error);
    }
  }

  getAverageTime(operation: string): number {
    const metrics = this.metrics.get(operation);
    if (!metrics || metrics.length === 0) return 0;

    return metrics.reduce((sum, value) => sum + value, 0) / metrics.length;
  }
}
```

---

## 📊 测试策略

### 1. 单元测试

#### 1.1 后端测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use axum_test_helper::TestClient;

    #[tokio::test]
    async fn test_compile_rust_code() {
        let app = create_app();
        let client = TestClient::new(app);

        let request = CompileRequest {
            code: r#"
                fn main() {
                    println!("Hello, World!");
                }
            "#.to_string(),
            edition: "2021".to_string(),
            features: vec![],
        };

        let response = client
            .post("/api/compile")
            .json(&request)
            .send()
            .await;

        assert_eq!(response.status(), 200);

        let result: CompileResponse = response.json().await;
        assert!(result.success);
        assert!(result.output.contains("Hello, World!"));
    }

    #[tokio::test]
    async fn test_compile_with_errors() {
        let app = create_app();
        let client = TestClient::new(app);

        let request = CompileRequest {
            code: "fn main() { invalid_syntax }".to_string(),
            edition: "2021".to_string(),
            features: vec![],
        };

        let response = client
            .post("/api/compile")
            .json(&request)
            .send()
            .await;

        assert_eq!(response.status(), 200);

        let result: CompileResponse = response.json().await;
        assert!(!result.success);
        assert!(!result.errors.is_empty());
    }
}
```

#### 1.2 前端测试

```typescript
// 代码编辑器测试
import { render, screen, fireEvent, waitFor } from '@testing-library/react';
import { CodeEditor } from './CodeEditor';

describe('CodeEditor', () => {
  const mockOnCodeChange = jest.fn();
  const mockOnRun = jest.fn();

  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('renders code editor with initial code', () => {
    render(
      <CodeEditor
        initialCode="fn main() {}"
        onCodeChange={mockOnCodeChange}
        onRun={mockOnRun}
      />
    );

    expect(screen.getByRole('textbox')).toBeInTheDocument();
  });

  it('calls onCodeChange when code is modified', async () => {
    render(
      <CodeEditor
        initialCode="fn main() {}"
        onCodeChange={mockOnCodeChange}
        onRun={mockOnRun}
      />
    );

    const editor = screen.getByRole('textbox');
    fireEvent.change(editor, { target: { value: 'fn main() { println!("test"); }' } });

    await waitFor(() => {
      expect(mockOnCodeChange).toHaveBeenCalledWith('fn main() { println!("test"); }');
    });
  });

  it('executes code when run button is clicked', async () => {
    // Mock fetch
    global.fetch = jest.fn().mockResolvedValue({
      ok: true,
      json: () => Promise.resolve({
        success: true,
        output: 'Hello, World!',
        errors: [],
        warnings: []
      })
    });

    render(
      <CodeEditor
        initialCode="fn main() { println!(\"Hello, World!\"); }"
        onCodeChange={mockOnCodeChange}
        onRun={mockOnRun}
      />
    );

    const runButton = screen.getByText('Run Code');
    fireEvent.click(runButton);

    await waitFor(() => {
      expect(global.fetch).toHaveBeenCalledWith('/api/compile', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          code: 'fn main() { println!("Hello, World!"); }',
          language: 'rust'
        })
      });
    });
  });
});
```

### 2. 集成测试

#### 2.1 端到端测试

```typescript
// Playwright 端到端测试
import { test, expect } from '@playwright/test';

test.describe('Interactive Documentation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/docs/interactive');
  });

  test('should compile and run Rust code', async ({ page }) => {
    // 输入代码
    await page.fill('[data-testid="code-editor"]', `
      fn main() {
          println!("Hello from interactive docs!");
      }
    `);

    // 点击运行按钮
    await page.click('[data-testid="run-button"]');

    // 等待输出
    await expect(page.locator('[data-testid="output"]')).toContainText('Hello from interactive docs!');
  });

  test('should show compilation errors', async ({ page }) => {
    // 输入错误代码
    await page.fill('[data-testid="code-editor"]', 'fn main() { invalid_syntax }');

    // 点击运行按钮
    await page.click('[data-testid="run-button"]');

    // 检查错误信息
    await expect(page.locator('[data-testid="error-message"]')).toBeVisible();
  });

  test('should progress through tutorial steps', async ({ page }) => {
    // 开始教程
    await page.click('[data-testid="start-tutorial"]');

    // 完成第一步
    await page.fill('[data-testid="step-code"]', 'fn main() { println!("Step 1"); }');
    await page.click('[data-testid="next-step"]');

    // 验证进度
    await expect(page.locator('[data-testid="progress-bar"]')).toHaveAttribute('style', /width: 50%/);
  });
});
```

---

## 🎯 成功指标

### 1. 用户体验指标

#### 1.1 参与度指标

- **代码执行次数**: 目标 10,000+ 次/月
- **教程完成率**: 目标 70%+
- **平均会话时长**: 目标 15+ 分钟
- **用户留存率**: 目标 60% (7天)

#### 1.2 学习效果指标

- **概念理解率**: 目标 85%+
- **实践成功率**: 目标 80%+
- **错误恢复率**: 目标 90%+
- **学习路径完成率**: 目标 75%+

### 2. 技术性能指标

#### 2.1 响应性能

- **代码编译时间**: < 2秒
- **页面加载时间**: < 1秒
- **交互响应时间**: < 100ms
- **API 响应时间**: < 500ms

#### 2.2 可用性指标

- **系统可用性**: 99.9%
- **错误率**: < 0.1%
- **并发用户支持**: 1,000+
- **数据一致性**: 100%

---

## 📞 项目联系

**项目负责人**: 交互式文档团队
**技术负责人**: 前端架构师
**后端负责人**: Rust 工程师
**UI/UX 负责人**: 用户体验设计师

**联系方式**:

- **邮箱**: <interactive-docs@otlp-rust.org>
- **GitHub**: <https://github.com/otlp-rust/interactive-docs>
- **讨论区**: <https://github.com/otlp-rust/interactive-docs/discussions>
- **Slack**: #interactive-docs

---

## 🙏 致谢

感谢所有参与交互式文档系统开发的团队成员。特别感谢：

- **前端开发团队**: 实现了优秀的用户界面
- **后端开发团队**: 构建了稳定的服务架构
- **设计团队**: 创造了直观的用户体验
- **测试团队**: 确保了系统的质量
- **社区贡献者**: 提供了宝贵的反馈和建议

---

**实现方案版本**: v1.0.0
**最后更新**: 2025年1月
**状态**: 开发中

🎮 **让我们一起打造最棒的交互式文档体验！** 🚀
