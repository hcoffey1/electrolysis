//https://github.com/TheAlgorithms/Rust
use std::cmp::min;
use std::cmp::Ordering;
use std::cmp::PartialEq;

pub fn linear_search<T: PartialEq>(item: &T, arr: &[T]) -> Option<usize> {
    for (i, data) in arr.iter().enumerate() {
        if item == data {
            return Some(i);
        }
    }

    None
}

pub fn binary_search<T: Ord>(item: &T, arr: &[T]) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;

        match item.cmp(&arr[mid]) {
            Ordering::Less => right = mid,
            Ordering::Equal => return Some(mid),
            Ordering::Greater => left = mid + 1,
        }
    }
    None
}

pub fn exponential_search<T: Ord>(item: &T, arr: &[T]) -> Option<usize> {
    let len = arr.len();
    if len == 0 {
        return None;
    }
    let mut upper = 1;
    while (upper < len) && (&arr[upper] <= item) {
        upper *= 2;
    }
    if upper > len {
        upper = len
    }

    // binary search
    let mut lower = upper / 2;
    while lower < upper {
        let mid = lower + (upper - lower) / 2;

        match item.cmp(&arr[mid]) {
            Ordering::Less => upper = mid,
            Ordering::Equal => return Some(mid),
            Ordering::Greater => lower = mid + 1,
        }
    }
    None
}

pub fn jump_search<T: Ord>(item: &T, arr: &[T]) -> Option<usize> {
    let len = arr.len();
    if len == 0 {
        return None;
    }
    let mut step = (len as f64).sqrt() as usize;
    let mut prev = 0;

    while &arr[min(len, step) - 1] < item {
        prev = step;
        step += (len as f64).sqrt() as usize;
        if prev >= len {
            return None;
        }
    }
    while &arr[prev] < item {
        prev += 1;
        if prev == min(step, len) {
            return None;
        }
    }
    if &arr[prev] == item {
        return Some(prev);
    }
    None
}
/*
   pub fn fibonacci_search<i32: Ord>(item: &i32, arr: &[i32]) -> Option<usize> {
   let len = arr.len();
   if len == 0 {
   return None;
   }
   let mut start = -1;

   let mut f0 = 0;
   let mut f1 = 1;
   let mut f2 = 1;
   while f2 < len {
   f0 = f1;
   f1 = f2;
   f2 = f0 + f1;
   }
   while f2 > 1 {
   let index = min((f0 as isize + start) as usize, len - 1);
   match item.cmp(&arr[index]) {
   Ordering::Less => {
   f2 = f0;
   f1 -= f0;
   f0 = f2 - f1;
   }
   Ordering::Equal => return Some(index),
   Ordering::Greater => {
   f2 = f1;
   f1 = f0;
   f0 = f2 - f1;
   start = index as isize;
   }
   }
   }
   if (f1 != 0) && (&arr[len - 1] == item) {
   return Some(len - 1);
   }
   None
   }*/
