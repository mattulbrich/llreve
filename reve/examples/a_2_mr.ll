; ModuleID = 'a_2_mr.bc'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: nounwind uwtable
define i32 @f(i32 %n) #0 {
  br label %1

; <label>:1                                       ; preds = %8, %0
  %i.0 = phi i32 [ 0, %0 ], [ %9, %8 ]
  %sum.0 = phi i32 [ 0, %0 ], [ %sum.1, %8 ]
  %2 = icmp sle i32 %i.0, 10
  br i1 %2, label %3, label %10

; <label>:3                                       ; preds = %1
  call void @__mark(i32 0)
  %4 = icmp ne i32 %i.0, 1
  br i1 %4, label %5, label %7

; <label>:5                                       ; preds = %3
  %6 = add nsw i32 %sum.0, %i.0
  br label %7

; <label>:7                                       ; preds = %5, %3
  %sum.1 = phi i32 [ %6, %5 ], [ %sum.0, %3 ]
  br label %8

; <label>:8                                       ; preds = %7
  %9 = add nsw i32 %i.0, 1
  br label %1

; <label>:10                                      ; preds = %1
  ret i32 %i.0
}

declare void @__mark(i32) #1

attributes #0 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = !{!"Ubuntu clang version 3.7.0-svn247539-1~exp1 (branches/release_37) (based on LLVM 3.7.0)"}