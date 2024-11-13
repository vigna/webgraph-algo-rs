/// The results produced by calling [`compute_directed`](super::OutputLevel::compute_directed)
/// on [`All`](super::All).
pub struct All {
    /// The forward eccentricities
    pub forward_eccentricities: Box<[usize]>,
    /// The backward eccentricities
    pub backward_eccentricities: Box<[usize]>,
    /// The diameter.
    pub diameter: usize,
    /// The radius.
    pub radius: usize,
    /// A vertex whose eccentricity equals the diameter.
    pub diametral_vertex: usize,
    /// A vertex whose eccentrivity equals the radius.
    pub radial_vertex: usize,
    /// Number of iterations before the radius was found.
    pub radius_iterations: usize,
    /// Number of iterations before the diameter was found.
    pub diameter_iterations: usize,
    /// Number of iterations before all forward eccentricities were found.
    pub forward_iterations: usize,
    /// Number of iterations before all eccentricities were found.
    pub all_iterations: usize,
}

/// The results produced by calling [`compute_directed`](super::OutputLevel::compute_directed)
/// on [`AllForward`](super::AllForward).
pub struct AllForward {
    /// The forward eccentricities
    pub forward_eccentricities: Box<[usize]>,
    /// The diameter.
    pub diameter: usize,
    /// The radius.
    pub radius: usize,
    /// A vertex whose eccentricity equals the diameter.
    pub diametral_vertex: usize,
    /// A vertex whose eccentrivity equals the radius.
    pub radial_vertex: usize,
    /// Number of iterations before the radius was found.
    pub radius_iterations: usize,
    /// Number of iterations before the diameter was found.
    pub diameter_iterations: usize,
    /// Number of iterations before all forward eccentricities are found.
    pub forward_iterations: usize,
}

/// The results produced by calling [`compute_directed`](super::OutputLevel::compute_directed)
/// on [`RadiusDiameter`](super::RadiusDiameter).
pub struct RadiusDiameter {
    /// The diameter.
    pub diameter: usize,
    /// The radius.
    pub radius: usize,
    /// A vertex whose eccentricity equals the diameter.
    pub diametral_vertex: usize,
    /// A vertex whose eccentrivity equals the radius.
    pub radial_vertex: usize,
    /// Number of iterations before the radius was found.
    pub radius_iterations: usize,
    /// Number of iterations before the diameter was found.
    pub diameter_iterations: usize,
}

/// The results produced by calling [`compute_directed`](super::OutputLevel::compute_directed)
/// on [`Diameter`](super::Diameter).
pub struct Diameter {
    /// The diameter.
    pub diameter: usize,
    /// A vertex whose eccentricity equals the diameter.
    pub diametral_vertex: usize,
    /// Number of iterations before the diameter was found.
    pub diameter_iterations: usize,
}

/// The results produced by calling [`compute_directed`](super::OutputLevel::compute_directed)
/// on [`Radius`](super::Radius).
pub struct Radius {
    /// The radius.
    pub radius: usize,
    /// A vertex whose eccentricity equals the radius.
    pub radial_vertex: usize,
    /// Number of iterations before the radius was found.
    pub radius_iterations: usize,
}
