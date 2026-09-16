/-
Authors: Yuhang Xie
-/

import Moran.Moran

/-!
Print the main Moran theorem statements and their transitive axiom dependencies.
-/

#check Moran.exists_moran_measure
#check Moran.spectralMoranData_dimensions_eq
#check Moran.spectralMoranData_fourier_decay
#check Moran.spectralMoranData_has_spectrum
#check Moran.spectralMoranSpectrum_countable
#check Moran.spectralMoranData_is_salem

#print axioms Moran.exists_moran_measure
#print axioms Moran.spectralMoranData_dimensions_eq
#print axioms Moran.spectralMoranData_fourier_decay
#print axioms Moran.spectralMoranData_has_spectrum
#print axioms Moran.spectralMoranSpectrum_countable
#print axioms Moran.spectralMoranData_is_salem
