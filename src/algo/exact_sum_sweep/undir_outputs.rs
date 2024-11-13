/// The results produced by calling [`compute_undirected`](super::OutputLevel::compute_undirected)
/// on [`All`](super::All).
pub struct All {
    /// The eccentricities
    pub eccentricities: Box<[usize]>,
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
    /// Number of iterations before all eccentricities were found.
    pub iterations: usize,
}

/// The results produced by calling [`compute_undirected`](super::OutputLevel::compute_undirected)
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
}

/// The results produced by calling [`compute_undirected`](super::OutputLevel::compute_undirected)
/// on [`Diameter`](super::Diameter).
pub struct Diameter {
    /// The diameter.
    pub diameter: usize,
    /// The radius.
    /// A vertex whose eccentricity equals the diameter.
    pub diametral_vertex: usize,
    /// Number of iterations before the diameter was found.
    pub diameter_iterations: usize,
}

/// The results produced by calling [`compute_undirected`](super::OutputLevel::compute_undirected)
/// on [`Radius`](super::Radius).
pub struct Radius {
    /// The radius.
    pub radius: usize,
    /// A vertex whose eccentrivity equals the radius.
    pub radial_vertex: usize,
    /// Number of iterations before the radius was found.
    pub radius_iterations: usize,
}
