type proof_step =
    Cut of { name_theorem : string; name_in_context : string;
      and_then : string;
    }
  | LeftForall of { to_specialize : string; term : string; and_then : string;
    }
  | RightRefl
  | RightSubst of { backward : bool; rw : string; focus : string;
      and_then : string;
    }
val generate_proof : string -> (string * proof_step) list