# HEAPVERSE: Explore. Build. Break. Understand.

An interactive laboratory for Heaps, Binary Heaps, Priority Queues and Heap Sort.
Every operation (insert, extract, heapify, build heap, heap sort) runs on a real array-based heap and is animated step by step.

## Run locally

```bash
npm install
npm run dev        # http://localhost:5173
npm run build      # production build in dist/
```

## Deploy to GitHub Pages

1. Push this folder to a GitHub repository (branch `main`).
2. In the repository go to **Settings > Pages** and set **Source** to **GitHub Actions**.
3. Every push to `main` builds and publishes the site automatically (`.github/workflows/deploy.yml`).

## Tech

React 18, Vite, Tailwind CSS, Lucide React, Recharts. The Heap Mentor is rule-based (no AI API is used).
