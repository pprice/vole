// src/bench/stats.rs
//
// Statistics computation for benchmark results.

use serde::Serialize;

/// Computed statistics from sample values
#[derive(Debug, Clone, Serialize)]
pub struct Stats {
    pub mean: f64,
    pub min: f64,
    pub max: f64,
    pub std_dev: f64,
    pub count: usize,
}

impl Stats {
    /// Compute statistics from f64 samples
    pub fn from_samples(samples: &[f64]) -> Self {
        if samples.is_empty() {
            return Self {
                mean: 0.0,
                min: 0.0,
                max: 0.0,
                std_dev: 0.0,
                count: 0,
            };
        }

        let count = samples.len();
        let sum: f64 = samples.iter().sum();
        let mean = sum / count as f64;

        let min = samples.iter().cloned().fold(f64::INFINITY, f64::min);
        let max = samples.iter().cloned().fold(f64::NEG_INFINITY, f64::max);

        // Sample standard deviation (n-1 denominator)
        let variance = if count > 1 {
            let sum_sq: f64 = samples.iter().map(|x| (x - mean).powi(2)).sum();
            sum_sq / (count - 1) as f64
        } else {
            0.0
        };
        let std_dev = variance.sqrt();

        Self {
            mean,
            min,
            max,
            std_dev,
            count,
        }
    }

    /// Compute statistics from u64 samples (converted to f64)
    pub fn from_u64_samples(samples: &[u64]) -> Self {
        let f64_samples: Vec<f64> = samples.iter().map(|&x| x as f64).collect();
        Self::from_samples(&f64_samples)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stats_basic() {
        let samples = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let stats = Stats::from_samples(&samples);

        assert_eq!(stats.mean, 3.0);
        assert_eq!(stats.min, 1.0);
        assert_eq!(stats.max, 5.0);
        assert_eq!(stats.count, 5);
        // std_dev of [1,2,3,4,5] is sqrt(2.5) ≈ 1.58
        assert!((stats.std_dev - 1.58).abs() < 0.01);
    }

    #[test]
    fn test_stats_single_sample() {
        let samples = vec![42.0];
        let stats = Stats::from_samples(&samples);

        assert_eq!(stats.mean, 42.0);
        assert_eq!(stats.min, 42.0);
        assert_eq!(stats.max, 42.0);
        assert_eq!(stats.std_dev, 0.0);
    }

    #[test]
    fn test_stats_empty() {
        let samples: Vec<f64> = vec![];
        let stats = Stats::from_samples(&samples);

        assert_eq!(stats.mean, 0.0);
        assert_eq!(stats.count, 0);
    }

    #[test]
    fn test_stats_from_u64() {
        let samples = vec![10u64, 20, 30, 40, 50];
        let stats = Stats::from_u64_samples(&samples);

        assert_eq!(stats.mean, 30.0);
        assert_eq!(stats.min, 10.0);
        assert_eq!(stats.max, 50.0);
    }
}
