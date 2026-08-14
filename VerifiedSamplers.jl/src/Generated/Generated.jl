# This submodule assembles code emitted from `formal/`.
module Generated

include("FiniteCore.jl")

using .FiniteCore: categorical_index!, finite_mh_step!, two_state_mh_step!

export categorical_index!, finite_mh_step!, two_state_mh_step!

end
