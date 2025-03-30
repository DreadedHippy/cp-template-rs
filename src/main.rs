#![allow(unused)]
use std::{cell::RefCell, clone, cmp::{min, Ordering, Reverse}, collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque}, fmt::{format, Binary}, hash::{Hash, Hasher}, i32, i64, io::Cursor, mem::swap, ops::{Add, AddAssign}, rc::Rc, result, usize};
use std::ops::Bound::{Included, Excluded};


const KX: u32 = 123456789;
const KY: u32 = 362436069;
const KZ: u32 = 521288629;
const KW: u32 = 88675123;


// Random
pub struct Rand {
    x: u32, y: u32, z: u32, w: u32
}

impl Rand{
    pub fn new(seed: u32) -> Rand {
        Rand{
            x: KX^seed, y: KY^seed,
            z: KZ, w: KW
        }
    }

    // Xorshift 128, taken from German Wikipedia
    pub fn rand(&mut self) -> u32 {
        let t = self.x^self.x.wrapping_shl(11);
        self.x = self.y; self.y = self.z; self.z = self.w;
        self.w ^= self.w.wrapping_shr(19)^t^t.wrapping_shr(8);
        return self.w;
    }

    pub fn shuffle<T>(&mut self, a: &mut [T]) {
        if a.len()==0 {return;}
        let mut i = a.len()-1;
        while i>0 {
            let j = (self.rand() as usize)%(i+1);
            a.swap(i,j);
            i-=1;
        }
    }

    pub fn rand_range(&mut self, a: i32, b: i32) -> i32 {
        let m = (b-a+1) as u32;
        return a+(self.rand()%m) as i32;
    }

    pub fn rand_float(&mut self) -> f64 {
        (self.rand() as f64)/(<u32>::max_value() as f64)
    }
}


#[allow(unused)]
macro_rules! cina {
    ($t:tt) => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.split_whitespace()
            .map(|x| x.parse::<$t>().unwrap())
            .collect::<Vec<$t>>()
    }};
}


macro_rules! cin {
    ($t:tt) => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.trim().parse::<$t>().unwrap()
    }};
}

#[allow(unused)]
macro_rules! cins {
    () => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.trim().to_string()
    }};
}

#[allow(unused)]
macro_rules! cinc {
    () => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.trim().chars()
        .collect::<Vec<char>>()
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

type U = usize;
type I = isize;
type F = f64;

//*! PRE-COMPUTATION
//*! CAPACITY ERRORS
//*! USING `RETURN` INSTEAD OF `CONTINUE`
//*! NOT PROPERLY TESTING EDGE-CASES
//*! NOT READING DOCUMENTATION OF STD TOOLS PROPERLY E.G BTREESET::RANGE() PANIC CONDITIONS
//*! BINARY SEARCH ON SUBSTRING PROBLEMS
//*! NEIGHBORING NUMBERS: EXPAND/SHRINK INTERVAL WINDOW */
//*! BITMASKING: FORM YOUR TRUTH TABLES, USE U64
//*! THINK SIMPLY !!!

const MODULO: i64 = 1_000_000_007;

fn main() {

}

fn vec_to_string<T: ToString>(a: &Vec<T>) -> String {
    a.iter().map(|x| x.to_string() + " ").collect::<String>().trim().to_string()
}

pub fn prime_factorization(mut number:i128) -> BTreeMap<i128, i128> {
    let mut prime_factors: BTreeMap<i128, i128> = BTreeMap::new();

    // Step 1 : Divide by 2
    let mut freq:i128 = 0;

    // You can use number % 2 == 0 also,
    // but this method is much more efficient
    while number&1 == 0 {
        number >>=1;
        // Again, You can use number /= 2 also,
        // but this is much more efficient
        freq+=1;
    }

    if freq > 0 {
        prime_factors.insert(2, freq);
    }

    // Step 2 : start from 3, and go till square root of number
    let mut i = 3;
    while i*i <= number {

        // Step 3 : Check if i is factor of number
        if number%i==0 {
            freq = 0;
            while number%i==0 {
                number/=i;
                freq+=1;
            }
            prime_factors.insert(i, freq);
        }
        i+=2;
    }

    // Step 4 : Check if number become 1 or not
    if number > 1 {
        prime_factors.insert(number, 1);
    }

    return prime_factors;
}

// pub fn petr(rotations: &Vec<usize>, )

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
    (1..).take_while(|&x| x * x <= n).into_iter().filter(|&x| n % x == 0).flat_map(|x| if x == n/x {vec![x]} else {vec![x, n/x]}).collect::<Vec<u64>>()
}

// BITWISE OPERATIONS;
pub fn get_msb(n: u32) -> u32{
	32 - (n.leading_zeros() - 1)
}