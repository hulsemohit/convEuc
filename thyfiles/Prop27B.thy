theory Prop27B
	imports Geometry Prop27 angledistinct betweennotequal collinearorder collinearparallel inequalitysymmetric parallelflip parallelsymmetric
begin

theorem Prop27B:
	assumes "axioms"
		"ang_eq A E F E F D"
		"oppo_side A E F D"
	shows "parallel A E F D"
proof -
	have "A \<noteq> E" using angledistinct[OF `axioms` `ang_eq A E F E F D`] by blast
	obtain B where "bet A E B \<and> seg_eq E B A E" using extensionE[OF `axioms` `A \<noteq> E` `A \<noteq> E`]  by  blast
	have "bet A E B" using `bet A E B \<and> seg_eq E B A E` by blast
	have "F \<noteq> D" using angledistinct[OF `axioms` `ang_eq A E F E F D`] by blast
	have "D \<noteq> F" using inequalitysymmetric[OF `axioms` `F \<noteq> D`] .
	obtain C where "bet D F C \<and> seg_eq F C F D" using extensionE[OF `axioms` `D \<noteq> F` `F \<noteq> D`]  by  blast
	have "bet D F C" using `bet D F C \<and> seg_eq F C F D` by blast
	have "bet C F D" using betweennesssymmetryE[OF `axioms` `bet D F C`] .
	have "parallel A B C D" using Prop27[OF `axioms` `bet A E B` `bet C F D` `ang_eq A E F E F D` `oppo_side A E F D`] .
	have "col D F C" using collinear_b `axioms` `bet D F C \<and> seg_eq F C F D` by blast
	have "col C D F" using collinearorder[OF `axioms` `col D F C`] by blast
	have "parallel A B F D" using collinearparallel[OF `axioms` `parallel A B C D` `col C D F` `F \<noteq> D`] .
	have "parallel F D A B" using parallelsymmetric[OF `axioms` `parallel A B F D`] .
	have "parallel F D B A" using parallelflip[OF `axioms` `parallel F D A B`] by blast
	have "col A E B" using collinear_b `axioms` `bet A E B \<and> seg_eq E B A E` by blast
	have "col B A E" using collinearorder[OF `axioms` `col A E B`] by blast
	have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A E B`] by blast
	have "E \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> E`] .
	have "parallel F D E A" using collinearparallel[OF `axioms` `parallel F D B A` `col B A E` `E \<noteq> A`] .
	have "parallel F D A E" using parallelflip[OF `axioms` `parallel F D E A`] by blast
	have "parallel A E F D" using parallelsymmetric[OF `axioms` `parallel F D A E`] .
	thus ?thesis by blast
qed

end