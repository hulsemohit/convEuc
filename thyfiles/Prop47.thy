theory Prop47
	imports n8_2 Geometry NCorder Prop47B betweennotequal collinear4 collinearorder collinearright droppedperpendicularunique equalitysymmetric inequalitysymmetric oppositesideflip paralleldef2B planeseparation squareflip squareparallelogram
begin

theorem Prop47:
	assumes "axioms"
		"triangle A B C"
		"ang_right B A C"
		"square A B F G"
		"oppo_side G B A C"
		"square A C K H"
		"oppo_side H C A B"
		"square B C E D"
		"oppo_side D C B A"
	shows "\<exists> L M. parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> qua_eq_area A B F G B M L D \<and> qua_eq_area A C K H M C E L"
proof -
	obtain L M where "parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D" using Prop47B[OF `axioms` `triangle A B C` `ang_right B A C` `square A B F G` `oppo_side G B A C` `square B C E D` `oppo_side D C B A`]  by  blast
	have "parallelogram B M L D" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` by blast
	have "bet B M C" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` by blast
	have "parallelogram M C E L" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` by blast
	have "bet D L E" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` by blast
	have "ang_right D L A" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` by blast
	have "qua_eq_area A B F G B M L D" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` by blast
	have "\<not> col A B C" using triangle_f[OF `axioms` `triangle A B C`] .
	have "\<not> col A C B" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "triangle A C B" using triangle_b[OF `axioms` `\<not> col A C B`] .
	have "ang_right C A B" using n8_2[OF `axioms` `ang_right B A C`] .
	have "square C B D E" using squareflip[OF `axioms` `square B C E D`] .
	have "oppo_side D B C A" using oppositesideflip[OF `axioms` `oppo_side D C B A`] .
	have "parallelogram B C E D" using squareparallelogram[OF `axioms` `square B C E D`] .
	have "parallel B C E D" using parallelogram_f[OF `axioms` `parallelogram B C E D`] by blast
	have "tarski_parallel B C E D" using paralleldef2B[OF `axioms` `parallel B C E D`] .
	have "same_side E D B C" using tarski_parallel_f[OF `axioms` `tarski_parallel B C E D`] by blast
	have "oppo_side E B C A" using planeseparation[OF `axioms` `same_side E D B C` `oppo_side D B C A`] .
	have "triangle A C B \<and> ang_right C A B \<and> square A C K H \<and> oppo_side H C A B \<and> square A B F G \<and> oppo_side G B A C \<and> square C B D E \<and> oppo_side E B C A" using `triangle A C B` `ang_right C A B` `square A C K H` `oppo_side H C A B` `square A B F G` `oppo_side G B A C` `square C B D E` `oppo_side E B C A` by blast
	obtain l m where "parallelogram C m l E \<and> bet C m B \<and> parallelogram m B D l \<and> bet E l D \<and> bet l m A \<and> ang_right E l A \<and> qua_eq_area A C K H C m l E" using Prop47B[OF `axioms` `triangle A C B` `ang_right C A B` `square A C K H` `oppo_side H C A B` `square C B D E` `oppo_side E B C A`]  by  blast
	have "bet E l D" using `parallelogram C m l E \<and> bet C m B \<and> parallelogram m B D l \<and> bet E l D \<and> bet l m A \<and> ang_right E l A \<and> qua_eq_area A C K H C m l E` by blast
	have "bet l m A" using `parallelogram C m l E \<and> bet C m B \<and> parallelogram m B D l \<and> bet E l D \<and> bet l m A \<and> ang_right E l A \<and> qua_eq_area A C K H C m l E` by blast
	have "qua_eq_area A C K H C m l E" using `parallelogram C m l E \<and> bet C m B \<and> parallelogram m B D l \<and> bet E l D \<and> bet l m A \<and> ang_right E l A \<and> qua_eq_area A C K H C m l E` by blast
	have "E \<noteq> D" using betweennotequal[OF `axioms` `bet E l D`] by blast
	have "D \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> D`] .
	have "ang_right E l A" using `parallelogram C m l E \<and> bet C m B \<and> parallelogram m B D l \<and> bet E l D \<and> bet l m A \<and> ang_right E l A \<and> qua_eq_area A C K H C m l E` by blast
	have "col E l D" using collinear_b `axioms` `parallelogram C m l E \<and> bet C m B \<and> parallelogram m B D l \<and> bet E l D \<and> bet l m A \<and> ang_right E l A \<and> qua_eq_area A C K H C m l E` by blast
	have "col D L E" using collinear_b `axioms` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` by blast
	have "col D E L" using collinearorder[OF `axioms` `col D L E`] by blast
	have "col D E l" using collinearorder[OF `axioms` `col E l D`] by blast
	have "col E l L" using collinear4[OF `axioms` `col D E l` `col D E L` `D \<noteq> E`] .
	have "L \<noteq> E" using betweennotequal[OF `axioms` `bet D L E`] by blast
	have "E \<noteq> L" using inequalitysymmetric[OF `axioms` `L \<noteq> E`] .
	have "ang_right E L A" using collinearright[OF `axioms` `ang_right D L A` `col D L E` `E \<noteq> L`] .
	have "l = L" using droppedperpendicularunique[OF `axioms` `ang_right E l A` `ang_right E L A` `col E l L`] .
	have "L = l" using equalitysymmetric[OF `axioms` `l = L`] .
	have "bet L m A" using `bet l m A` `l = L` by blast
	have "bet C m B" using `parallelogram C m l E \<and> bet C m B \<and> parallelogram m B D l \<and> bet E l D \<and> bet l m A \<and> ang_right E l A \<and> qua_eq_area A C K H C m l E` by blast
	have "bet L M A" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` by blast
	have "bet C M B" using betweennesssymmetryE[OF `axioms` `bet B M C`] .
	have "col L m A" using collinear_b `axioms` `bet L m A` by blast
	have "col L M A" using collinear_b `axioms` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` by blast
	have "col L A m" using collinearorder[OF `axioms` `col L m A`] by blast
	have "col L A M" using collinearorder[OF `axioms` `col L M A`] by blast
	have "L \<noteq> A" using betweennotequal[OF `axioms` `bet L M A`] by blast
	have "col A m M" using collinear4[OF `axioms` `col L A m` `col L A M` `L \<noteq> A`] .
	have "col M m A" using collinearorder[OF `axioms` `col A m M`] by blast
	have "col B M C" using collinear_b `axioms` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` by blast
	have "col C B M" using collinearorder[OF `axioms` `col B M C`] by blast
	have "col C m B" using collinear_b `axioms` `parallelogram C m l E \<and> bet C m B \<and> parallelogram m B D l \<and> bet E l D \<and> bet l m A \<and> ang_right E l A \<and> qua_eq_area A C K H C m l E` by blast
	have "col C B m" using collinearorder[OF `axioms` `col C m B`] by blast
	have "C \<noteq> B" using betweennotequal[OF `axioms` `bet C M B`] by blast
	have "col B M m" using collinear4[OF `axioms` `col C B M` `col C B m` `C \<noteq> B`] .
	have "col M m B" using collinearorder[OF `axioms` `col B M m`] by blast
	have "\<not> (M \<noteq> m)"
	proof (rule ccontr)
		assume "\<not> (\<not> (M \<noteq> m))"
hence "M \<noteq> m" by blast
		have "col m M A" using collinearorder[OF `axioms` `col A m M`] by blast
		have "col m M B" using collinearorder[OF `axioms` `col B M m`] by blast
		have "m \<noteq> M" using inequalitysymmetric[OF `axioms` `M \<noteq> m`] .
		have "col M A B" using collinear4[OF `axioms` `col m M A` `col m M B` `m \<noteq> M`] .
		have "col M B A" using collinearorder[OF `axioms` `col M A B`] by blast
		have "col M B C" using collinearorder[OF `axioms` `col B M C`] by blast
		have "M \<noteq> B" using betweennotequal[OF `axioms` `bet C M B`] by blast
		have "col B A C" using collinear4[OF `axioms` `col M B A` `col M B C` `M \<noteq> B`] .
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "M = m" by blast
	have "qua_eq_area A C K H C M l E" using `qua_eq_area A C K H C m l E` `M = m` by blast
	have "qua_eq_area A C K H C M L E" using `qua_eq_area A C K H C M l E` `l = L` by blast
	have "qua_eq_area A C K H M C E L" using EFpermutationE[OF `axioms` `qua_eq_area A C K H C M L E`] by blast
	have "parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> qua_eq_area A B F G B M L D \<and> qua_eq_area A C K H M C E L" using `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` `parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A \<and> qua_eq_area A B F G B M L D` `qua_eq_area A C K H M C E L` by blast
	thus ?thesis by blast
qed

end