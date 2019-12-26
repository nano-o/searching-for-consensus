some sig proc { }
some sig State {  }

// We encode the transition function of an object as a relation f:(State -> proc)->(State -> proc) (i.e. the object operations take processor ids as argument and return processor ids).
// The predicate "function" below asserts that the relation f is a function
pred function[f:(State -> proc)->(State -> proc)] {
	all s, s2, s3 : State, p, p2,p3:proc | (s->p)->(s2->p2) in f && (s->p)->(s3->p3) in f => (s2 = s3 && p2 = p3)
}
// Predicate "enabled" asserts that the relation f is total.
pred enabled[f:(State -> proc)->(State -> proc)] {
	all s : State |  all p:proc | some s2 : State, p2 :proc | (s->p)->(s2->p2)  in f
}

// We look for an object that can solve (3,2)-set-consensus in a single shot.

// Predicate "boundary" encodes the validity condition of set-consensus.
pred boundary[f:(State -> proc)->(State -> proc), init:State] {
				(all s: State, p1, q2 : proc | (init->p1)->(s->q2) in f => (p1 = q2))
				&& (all s1, s2: State, p1, p2, q1, q2: proc | 
					(init->p1)->(s1->q1) in f && (s1->p2)->(s2->q2) in f && p1 != p2 => (q2 = p1 || q2 = p2))
}

// The "set_cons" predicate is true when the object solves (3,2)-set-consensus single-shot. To express that we just require that at least two outputs be equal.
pred set_cons[f:(State -> proc)->(State -> proc), init:State] {
	(all s1, s2, s3 : State, p1, p2, p3, q1, q2,q3 : proc |
					 (init->p1)->(s1->q1) in f && (s1->p2)->(s2->q2) in f && (s2->p3)->(s3->q3) in f && p1 != p2 && p1 != p3 && p2 != p3 
							=> (q1 = q2 || q1 = q3 || q2 = q3))
}

// Predicate no_cons says that any two operations applied one after the other result in the same state regardless of their order, 
// and that one of them returns the same result regardless of their order. 
// This implies that consensus cannot be solved, but a weaker condition might also work (i.e. the condition below is only sufficient)..
pred no_cons[f:(State -> proc)->(State -> proc)] {
	all s1 : State | all p1,p2:proc | all s2,s3,s4,s5 : State, q1,q2,q3,q4: proc |
		(s1->p1)->(s2->q1) in f && (s2->p2)->(s3->q2) in f && (s1->p2)->(s4->q3) in f && (s4->p1)->(s5->q4) in f
			=> (s3 = s5 && (q1=q4 || q2 = q3))
}

// Now find a transition function satisfying all the constraints (fixing the number of states)
run { some f : (State -> proc) -> (State -> proc) | some init : State |
	set_cons[f,init] && boundary[f,init] && no_cons[f] && enabled[f] && function[f]
} for 0 but exactly 8 State, exactly 3 proc
