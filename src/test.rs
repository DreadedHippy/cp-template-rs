use std::{clone, cmp::min, collections::{vec_deque, HashMap, HashSet, VecDeque}, fmt::format, fs::{self, File}, hash::Hash, io::Read, ops::{Add, AddAssign, ControlFlow}, result, string, vec};

const LOWERCASE_ENGLISH_ALPHABETS: [char; 26] = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'];

#[derive(Debug)]
struct Coordinates(i32, i32);

impl Add for Coordinates {
    type Output = Coordinates;

    fn add(self, other: Coordinates) -> Coordinates {
        Coordinates(self.0 + other.0, self.1 + other.1)
    }
}

impl AddAssign for Coordinates {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
        self.1 += rhs.1;
    }
}

impl Coordinates {
    pub fn new() -> Self {
        Coordinates(0, 0)
    }

    pub fn from(raw: (i32, i32)) -> Self{
        Coordinates(raw.0, raw.1)
    }
}

// BITWISE OPERATIONS;
pub fn get_msb(n: u32) -> u32{
	32 - (n.leading_zeros() - 1)
}


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

macro_rules! read_str {
    () => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.trim().to_string()
    }};
}


macro_rules! read_joined_chars {
    ($t:tt) => {{
        let mut temp = String::new();
        std::io::stdin().read_line(&mut temp).expect("fail");
        temp.trim().chars()
        .collect::<Vec<$t>>()
    }};
}



//*! PRE-COMPUTATION
//*! CAPACITY ERRORS

#[derive(Debug)]
pub struct Tile {
    id: char,
    cost: usize,
    available: usize,
}

const MODULO: i64 = 1_000_000_007;

fn main() {
    
    let tests = read_t!(usize);

    'test_cases: for i in 0..tests {
        let info = read_line_t!(usize);
        let (a, b, mut r) = (info[0], info[1], info[2]);
        let a_s = format!("{:b}", a).chars().collect::<Vec<char>>();
        let b_s = format!("{:b}", b).chars().collect::<Vec<char>>();

        let len = a_s.len().min(b_s.len());

        let mut xor = 0;

        for i in (0..len).rev() {
            if a_s[i] == '1' && b_s[i] == '1' {
                if r > 2_usize.pow(i as u32) {
                    r-=2_usize.pow(i as u32);
                    xor+= 2_usize.pow(i as u32)
                } else {
                    break
                }
            }
        }

        println!("{}", ((a ^ xor) as i32 - (b ^ xor) as i32).abs())
    }
}

// fn search_through(adjacency_list: &HashMap<usize, Vec<(usize, usize)>>, distance: usize, n: usize, flags: &mut Vec<bool>, destination: usize, res: &mut usize, slowness_factors: &Vec<usize>) -> usize {
//     flags[n-1] = true;

//     let mut res = usize::MAX;

//     if n == destination {
//         return distance
//     }

//     let connections = adjacency_list.get(&n).unwrap();

//     for (city, road) in connections {
//         if flags[*city] == false {
//             let distance = distance + (road * slowness_factors[n-1]);
//             res = res.min(search_through(adjacency_list, distance, n, flags, destination, &mut res, slowness_factors))
//         }
//     }

//     return res

// }


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

fn solve(n: usize, k: usize) -> usize {
    if k <= n/2 {
        return (2 * k) - 1
    } else {
        2 * solve(n/2, k - (n/2))
    }
}

fn get_factors_functional(n: u64) -> Vec<u64> {
    (1..).take_while(|&x| x * x <= n).into_iter().filter(|&x| n % x == 0).collect::<Vec<u64>>()
}

// fn sum_digits(x: u32) -> u32 {
//     (x % 10) + (0..)
//         .scan(x, |num, _| {
//             *num /= 10;
//             Some(*num)
//         })
//         .take_while(|num| *num > 0)
//         .map(|num| num % 10)
//         .sum::<u32>()
// }