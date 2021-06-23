theory Prop41
	imports ETreflexive Geometry Prop37 collinearorder collinearparallel inequalitysymmetric parallelNC parallelflip parallelsymmetric
begin

theorem Prop41:
	assumes "axioms"
		"parallelogram A B C D"
		"col A D E"
	shows "tri_eq_area A B C E B C"
proof -
	have "parallel A B C D" using parallelogram_f[OF `axioms` `parallelogram A B C D`] by blast
	have "\<not> col A B C" using parallelNC[OF `axioms` `parallel A B C D`] by blast
	have "triangle A B C" using triangle_b[OF `axioms` `\<not> col A B C`] .
	consider "A = E"|"A \<noteq> E" by blast
	hence "tri_eq_area A B C E B C"
	proof (cases)
		assume "A = E"
		have "tri_eq_area A B C A B C" using ETreflexive[OF `axioms` `triangle A B C`] .
		have "tri_eq_area A B C E B C" using `tri_eq_area A B C A B C` `A = E` by blast
		thus ?thesis by blast
	next
		assume "A \<noteq> E"
		have "parallel A D B C" using parallelogram_f[OF `axioms` `parallelogram A B C D`] by blast
		have "col D A E" using collinearorder[OF `axioms` `col A D E`] by blast
		have "parallel B C A D" using parallelsymmetric[OF `axioms` `parallel A D B C`] .
		have "parallel B C D A" using parallelflip[OF `axioms` `parallel B C A D`] by blast
		have "E \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> E`] .
		have "parallel B C E A" using collinearparallel[OF `axioms` `parallel B C D A` `col D A E` `E \<noteq> A`] .
		have "parallel B C A E" using parallelflip[OF `axioms` `parallel B C E A`] by blast
		have "parallel A E B C" using parallelsymmetric[OF `axioms` `parallel B C A E`] .
		have "tri_eq_area A B C E B C" using Prop37[OF `axioms` `parallel A E B C`] .
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end