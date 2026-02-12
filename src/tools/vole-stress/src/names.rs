//! Verb-adjective-animal name generator for unique output directory names.
//!
//! Generates names like "blazing-swift-penguin", "soaring-cosmic-badger".

use rand::Rng;

/// Present-participle verbs for name generation.
const VERBS: &[&str] = &[
    "blazing",
    "soaring",
    "dashing",
    "gliding",
    "racing",
    "spinning",
    "leaping",
    "diving",
    "charging",
    "roaming",
    "drifting",
    "flowing",
    "humming",
    "pulsing",
    "surging",
    "whirling",
    "zooming",
    "flashing",
    "gleaming",
    "glowing",
    "shining",
    "sparking",
    "streaking",
    "beaming",
    "bounding",
    "climbing",
    "cruising",
    "darting",
    "floating",
    "flying",
    "hovering",
    "jumping",
    "rolling",
    "running",
    "sailing",
    "skating",
    "sliding",
    "sprinting",
    "striding",
    "swimming",
    "turning",
    "twisting",
    "winding",
    "arcing",
    "banking",
    "coasting",
    "falling",
    "landing",
    "lifting",
    "rising",
    "shifting",
];

/// Adjectives for name generation - selected for positive/neutral connotations
/// and reasonable length.
const ADJECTIVES: &[&str] = &[
    "swift",
    "cosmic",
    "bright",
    "silent",
    "nimble",
    "golden",
    "silver",
    "clever",
    "noble",
    "brave",
    "gentle",
    "fierce",
    "steady",
    "quiet",
    "bold",
    "calm",
    "quick",
    "sharp",
    "wild",
    "wise",
    "agile",
    "amber",
    "arctic",
    "azure",
    "bronze",
    "coral",
    "crystal",
    "dusty",
    "ember",
    "frosty",
    "gleaming",
    "hidden",
    "ivory",
    "jade",
    "keen",
    "lunar",
    "misty",
    "neon",
    "obsidian",
    "primal",
    "radiant",
    "scarlet",
    "tawny",
    "velvet",
    "wandering",
    "zephyr",
];

/// Animals for name generation - selected for memorability and variety.
const ANIMALS: &[&str] = &[
    "penguin", "badger", "falcon", "otter", "raven", "tiger", "wolf", "bear", "eagle", "hawk",
    "fox", "lynx", "owl", "puma", "stag", "crane", "finch", "heron", "cobra", "viper", "bison",
    "condor", "coyote", "dolphin", "gecko", "jaguar", "lemur", "mantis", "moose", "osprey",
    "panther", "python", "rabbit", "salmon", "shark", "sparrow", "turtle", "walrus", "wombat",
    "zebra",
];

/// Generate a random verb-adjective-animal name using the given RNG.
pub fn generate<R: Rng>(rng: &mut R) -> String {
    let verb_idx = rng.gen_range(0..VERBS.len());
    let adj_idx = rng.gen_range(0..ADJECTIVES.len());
    let animal_idx = rng.gen_range(0..ANIMALS.len());
    format!(
        "{}-{}-{}",
        VERBS[verb_idx], ADJECTIVES[adj_idx], ANIMALS[animal_idx]
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;

    #[test]
    fn generate_produces_three_part_name() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let name = generate(&mut rng);
        let parts: Vec<&str> = name.split('-').collect();
        assert_eq!(parts.len(), 3, "name should have 3 parts: {name}");
    }

    #[test]
    fn generate_is_deterministic_with_seed() {
        let mut rng1 = rand::rngs::StdRng::seed_from_u64(12345);
        let mut rng2 = rand::rngs::StdRng::seed_from_u64(12345);
        let name1 = generate(&mut rng1);
        let name2 = generate(&mut rng2);
        assert_eq!(name1, name2);
    }

    #[test]
    fn generate_varies_with_different_seeds() {
        let mut rng1 = rand::rngs::StdRng::seed_from_u64(111);
        let mut rng2 = rand::rngs::StdRng::seed_from_u64(222);
        let name1 = generate(&mut rng1);
        let name2 = generate(&mut rng2);
        // With different seeds, names should (almost certainly) differ
        assert_ne!(name1, name2);
    }

    #[test]
    fn word_lists_are_non_empty() {
        assert!(!VERBS.is_empty());
        assert!(!ADJECTIVES.is_empty());
        assert!(!ANIMALS.is_empty());
    }

    #[test]
    fn word_lists_have_no_empty_words() {
        for verb in VERBS {
            assert!(!verb.is_empty(), "verb should not be empty");
        }
        for adj in ADJECTIVES {
            assert!(!adj.is_empty(), "adjective should not be empty");
        }
        for animal in ANIMALS {
            assert!(!animal.is_empty(), "animal should not be empty");
        }
    }

    #[test]
    fn pool_size_is_large_enough() {
        let pool = VERBS.len() * ADJECTIVES.len() * ANIMALS.len();
        assert!(
            pool > 50_000,
            "pool should be >50k to avoid collisions, got {pool}"
        );
    }
}
