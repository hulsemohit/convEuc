theory Prop41
	imports Axioms Definitions Theorems
begin

theorem Prop41:
	assumes: `axioms`
		"parallelogram A B C D"
		"col A D E"
	shows: "tri_eq_area A B C E B C"
proof -
	have "parallel A B C D" sorry
	have "\<not> col A B C" using parallelNC[OF `axioms` `parallel A B C D`] by blast
	have "triangle A B C" sorry
	consider "A = E"|"A \<noteq> E" by blast
	hence tri_eq_area A B C E B C
	proof (cases)
		case 1
		have "tri_eq_area A B C A B C" using ETreflexive[OF `axioms` `triangle A B C`] .
		have "tri_eq_area A B C E B C" sorry
	next
		case 2
		have "parallel A D B C" sorry
		have "col D A E" using collinearorder[OF `axioms` `col A D E`] by blast
		have "parallel B C A D" using parallelsymmetric[OF `axioms` `parallel A D B C`] .
		have "parallel B C D A" using parallelflip[OF `axioms` `parallel B C A D`] by blast
		have "E \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> E`] .
		have "parallel B C E A" using collinearparallel[OF `axioms` `parallel B C D A` `col D A E` `E \<noteq> A`] .
		have "parallel B C A E" using parallelflip[OF `axioms` `parallel B C E A`] by blast
		have "parallel A E B C" using parallelsymmetric[OF `axioms` `parallel B C A E`] .
		have "tri_eq_area A B C E B C" using Prop37[OF `axioms` `parallel A E B C`] .
	next
	thus ?thesis by blast
qed

end