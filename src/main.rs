use std::{clone, cmp::min, collections::{BTreeSet, HashMap, HashSet, VecDeque}, fmt::format, mem::swap, ops::{Add, AddAssign}};
use std::ops::Bound::{Included, Excluded};

#[allow(unused)]
macro_rules! read_line_t {
    ($t:tt) => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.split_whitespace()
            .map(|x| x.parse::<$t>().unwrap())
            .collect::<Vec<$t>>()
    }};
}


macro_rules! read_t {
    ($t:tt) => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.trim().parse::<$t>().unwrap()
    }};
}

#[allow(unused)]
macro_rules! read_str {
    () => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.trim().to_string()
    }};
}

#[allow(unused)]
macro_rules! read_joined_chars {
    ($t:tt) => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.trim().chars()
        .collect::<Vec<$t>>()
    }};
}

#[allow(unused)]
macro_rules! tuple {
    [$xs:expr; 2] => {
        { let value = $xs; (value[0], value[1]) }
    };
    [$xs:expr; 3] => {
        { let value = $xs; (value[0], value[1], value[2]) }
    };
    [$xs:expr; 4] => {
        { let value = $xs; (value[0], value[1], value[2], value[3]) }
    };
    [$xs:expr; $t:ty ;2] => {
        { let value = $xs; (value[0] as $t, value[1] as $t) }
    };
    [$xs:expr; $t:ty; 3] => {
        { let value = $xs; (value[0] as $t, value[1] as $t, value[2] as $t) }
    };
    [$xs:expr; $t:ty; 4] => {
        { let value = $xs; (value[0] as $t, value[1] as $t, value[2] as $t, value[3] as $t) }
    };
}


//*! PRE-COMPUTATION
//*! CAPACITY ERRORS
//*! USING `RETURN` INSTEAD OF `CONTINUE`
//*! NOT PROPERLY TESTING EDGE-CASES
//*! NOT READING DOCUMENTATION OF STD TOOLS PROPERLY E.G BTREESET::RANGE() PANIC CONDITIONS
//*! BINARY SEARCH ON SUBSTRING PROBLEMS
const MODULO: i64 = 1_000_000_007;

fn main() {
    let t = read_t!(usize);

    for _ in 0..t {
        let n = read_t!(usize);

        solve(n);
    }
}


pub fn solve(n: usize) {
    if n == 1 {
        println!("? 0");
        if read_t!(i32) == 1 {
            println!("! 0")
        } else {
            println!("! 1")
        }

        return
    }
    if n == 2 {
        println!("? 01");
        if read_t!(i32) == 1 {
            println!("! 01");
            return
        }
        println!("? 00");
        if read_t!(i32) == 1 {
            println!("! 00");
            return
        }
        println!("? 10");
        if read_t!(i32) == 1 {
            println!("! 10");
            return;
        }

        println!("! 11");

        return
    }

    // binary search for no of max successive 0s;

    let mut l = 1; // 0 zeroes
    let mut r = n; // n zeroes


    let mut mid = (l + r)/2;

    while l <= r {
        let test = std::iter::repeat('0').take(mid).collect::<String>();

        println!("? {}", test);

        match read_t!(i32) {
            0 => r = mid - 1,
            1 => l = mid +  1,
            _ => {}
        }

        mid = (l + r)/2

    }

    // ------


    let mut start = std::iter::repeat('0').take(mid).collect::<String>();

    let mut reached_end = false;

    // append more to the bck
    while start.len() < n {
        println!("? {}{}", start, "1");

        let response = read_t!(i32);

        if response == 1 {
            start.push('1');
            continue;
        }

        if response == 0 {
            println!("? {}{}", start, "0");
            
            if read_t!(i32) == 1 {
                start.push('0');
            } else {

                // cannot append any more to the back, append '1' to the front and move,
                // we can do this because at the front is the initial number of max successive 0s
                // so we can not have any other 0 in front of it, and the length of string < n
                // hence a '1' can freely be appended to the front of the string
                start = format!("{}{}",1,start);
                reached_end = true;
                break;
            }
        }
    }

    if reached_end {
        
        while start.len() < n {
            println!("? {}{}", "1", start);

            if read_t!(i32) == 1 {
                start = format!("{}{}", "1", start);
            } else {
                start = format!("{}{}", "0", start);
            }
        }

    }

    println!("! {}", start);
}


// pub fn knapsack(w: usize, weights: Vec<usize>, profits: Vec<usize>, position: usize) {
//     // position = index + 1;
//     if position == 0 || W == 0{
//         return 0
//     }

//     if weights[position - 1] > W {
//         // if weight > knapsack capacity, skip
//         return knapsack(w, weights, profits, position - 1);
//     }
// }

fn isqrt(n: usize) -> usize {
    n == 0 && return n;
    let mut s = (n as f64).sqrt() as usize;
    s = (s + n / s) >> 1;
    if s * s > n { s - 1 } else { s }
}

fn perfect_sqrt(n: usize) -> isize {
    match n & 0xf {
        0 | 1 | 4 | 9 => {
            let t = isqrt(n);
            if t*t == n { t as isize } else { -1 }
        },
        _ => -1,
    }
}

fn is_prime(n:usize) -> bool{

    // Iterate from i = 2 to sqrt ( n )
    if n < 2 {
        return false
    }
    if n == 2 {
        return true
    }

    let mut i:usize = 2;
    while i*i<=n {
        // Return false if the number is divisible
        if n%i == 0 {
            return false;
        }
        i+=1;
    }

    // Return true finally
    return true;
}


pub fn lcm(n1: u64, n2: u64) -> u64 {
    let (mut x, mut y, mut rem) = (0, 0, 0);
    if (n1 > n2) {
        x = n1;
        y = n2;
    }
    else {
        x = n2;
        y = n1;
    }

    rem = x % y;

    while (rem != 0) {
        x = y;
        y = rem;
        rem = x % y;
    }

    n1 * n2 / y
}

pub fn gcd(mut u: u64, mut v: u64) -> u64 {
    // Base cases: gcd(n, 0) = gcd(0, n) = n
    if u == 0 {
        return v;
    } else if v == 0 {
        return u;
    }

    // Using identities 2 and 3:
    // gcd(2ⁱ u, 2ʲ v) = 2ᵏ gcd(u, v) with u, v odd and k = min(i, j)
    // 2ᵏ is the greatest power of two that divides both 2ⁱ u and 2ʲ v
    let i = u.trailing_zeros();  u >>= i;
    let j = v.trailing_zeros();  v >>= j;
    let k = min(i, j);

    loop {
        // u and v are odd at the start of the loop
        // debug_assert!(u % 2 == 1, "u = {} should be odd", u);
        // debug_assert!(v % 2 == 1, "v = {} should be odd", v);

        // Swap if necessary so u ≤ v
        if u > v {
            swap(&mut u, &mut v);
        }

        // Identity 4: gcd(u, v) = gcd(u, v-u) as u ≤ v and u, v are both odd 
        v -= u;
        // v is now even

        if v == 0 {
            // Identity 1: gcd(u, 0) = u
            // The shift by k is necessary to add back the 2ᵏ factor that was removed before the loop
            return u << k;
        }

        // Identity 3: gcd(u, 2ʲ v) = gcd(u, v) as u is odd
        v >>= v.trailing_zeros();
    }
}

pub fn modulo_non_zero(number: usize, base: usize) -> usize {
    match number % base {
        0 => base,
        k => k
    }
}

pub fn max_sub_array(nums: Vec<i64>) -> (i64, usize) {
    use std::cmp;
    
    let (mut curr_sum, mut global_sum) = (0, i64::MIN);
    let mut end_index = 0;
    
    for i in 0..nums.len() {
        curr_sum+= nums[i];
        let old = global_sum;
        global_sum = cmp::max(curr_sum, global_sum);
        if global_sum > old {
            end_index = i
        }
        
        if curr_sum < 0 {
            curr_sum = 0;
        }            
    }
    
    (global_sum, end_index)
}

fn get_factors_functional(n: u64) -> Vec<u64> {
    (1..).take_while(|&x| x * x <= n).into_iter().filter(|&x| n % x == 0).flat_map(|x| [x, n/x]).collect::<Vec<u64>>()
}

// BITWISE OPERATIONS;
pub fn get_msb(n: u32) -> u32{
	32 - (n.leading_zeros() - 1)
}