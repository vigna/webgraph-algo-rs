/// Enum representing the requested output of the *SumSweep* algorithm.
///
/// This has slightly different meaning for the [`directed`](`super::SumSweepDirectedDiameterRadius`)
/// implementation and the [`undirected`](`super::SumSweepUndirectedDiameterRadius`) one.
#[derive(PartialEq)]
pub enum SumSweepOutputLevel {
    /// Compute all the eccentricities of the graph.
    All,
    /// Compute all the forward eccentricities of the graph.
    ///
    /// This is equivalent to [`All`](`Self::All`) in the undirected case.
    AllForward,
    /// Computes both the diameter and the radius of the graph.
    RadiusDiameter,
    /// Computes the diameter of the graph.
    Diameter,
    /// Computers the radius of the graph.
    Radius,
}
