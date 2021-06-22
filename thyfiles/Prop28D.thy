theory Prop28D
	imports Axioms Definitions Theorems
begin

theorem Prop28D:
	assumes: `axioms`
		"bet E G H"
		"ang_eq E G B G H D"
		"same_side B D G H"
	shows: "parallel G B H D"
proof -
	have "\<not> col G H B" using sameside_f[OF `axioms` `same_side B D G H`] by blast
	have "\<not> col G H D" using sameside_f[OF `axioms` `same_side B D G H`] by blast
	have "H \<noteq> D" using NCdistinct[OF `axioms` `\<not> col G H D`] by blast
	have "D \<noteq> H" using inequalitysymmetric[OF `axioms` `H \<noteq> D`] .
	have "G \<noteq> B" using NCdistinct[OF `axioms` `\<not> col G H B`] by blast
	have "B \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> B`] .
	obtain A where "bet B G A \<and> seg_eq G A G B" using extensionE[OF `axioms` `B \<noteq> G` `G \<noteq> B`] by blast
	have "bet B G A" using `bet B G A \<and> seg_eq G A G B` by blast
	have "bet A G B" using betweennesssymmetryE[OF `axioms` `bet B G A`] .
	obtain C where "bet D H C \<and> seg_eq H C H D" using extensionE[OF `axioms` `D \<noteq> H` `H \<noteq> D`] by blast
	have "bet D H C" using `bet D H C \<and> seg_eq H C H D` by blast
	have "bet C H D" using betweennesssymmetryE[OF `axioms` `bet D H C`] .
	have "parallel A B C D" using Prop28A[OF `axioms` `bet A G B` `bet C H D` `bet E G H` `ang_eq E G B G H D` `same_side B D G H`] .
	have "col D H C" using collinear_b `axioms` `bet D H C \<and> seg_eq H C H D` by blast
	have "col C D H" using collinearorder[OF `axioms` `col D H C`] by blast
	have "H \<noteq> D" using NCdistinct[OF `axioms` `\<not> col G H D`] by blast
	have "parallel A B H D" using collinearparallel[OF `axioms` `parallel A B C D` `col C D H` `H \<noteq> D`] .
	have "parallel H D A B" using parallelsymmetric[OF `axioms` `parallel A B H D`] .
	have "col B G A" using collinear_b `axioms` `bet B G A \<and> seg_eq G A G B` by blast
	have "col A B G" using collinearorder[OF `axioms` `col B G A`] by blast
	have "parallel H D G B" using collinearparallel[OF `axioms` `parallel H D A B` `col A B G` `G \<noteq> B`] .
	have "parallel G B H D" using parallelsymmetric[OF `axioms` `parallel H D G B`] .
	thus ?thesis by blast
qed

end