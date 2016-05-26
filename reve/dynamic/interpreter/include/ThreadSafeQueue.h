#pragma once

#include <queue>
#include <mutex>
#include <condition_variable>

template <typename T> class ThreadSafeQueue {
  private:
    std::queue<T> q;
    std::mutex m;
    std::condition_variable cv;
  public:
    void push(T &&val) {
        {
            std::lock_guard<std::mutex> lock(m);
            q.push(val);
        }
        cv.notify_one();
    }
    T pop() {
        std::unique_lock<std::mutex> lock(m);
        while (q.empty()) {
            cv.wait(lock);
        }
        T r = q.front();
        q.pop();
        return r;
    }
};
