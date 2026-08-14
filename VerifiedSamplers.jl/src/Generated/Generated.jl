# This submodule assembles code emitted from `formal/`.
module Generated

include("FiniteCore.jl")

using .FiniteCore: categorical_index!, two_state_mh_step!

export categorical_index!, two_state_mh_step!

end
