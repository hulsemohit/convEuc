theory Prop28D
	imports Geometry NCdistinct Prop28A collinearorder collinearparallel inequalitysymmetric parallelsymmetric
begin

theorem(in euclidean_geometry) Prop28D:
	assumes 
		"bet E G H"
		"ang_eq E G B G H D"
		"same_side B D G H"
	shows "parallel G B H D"
proof -
	have "\<not> col G H B" using sameside_f[OF `same_side B D G H`] by blast
	have "\<not> col G H D" using sameside_f[OF `same_side B D G H`] by blast
	have "H \<noteq> D" using NCdistinct[OF `\<not> col G H D`] by blast
	have "D \<noteq> H" using inequalitysymmetric[OF `H \<noteq> D`] .
	have "G \<noteq> B" using NCdistinct[OF `\<not> col G H B`] by blast
	have "B \<noteq> G" using inequalitysymmetric[OF `G \<noteq> B`] .
	obtain A where "bet B G A \<and> seg_eq G A G B" using extensionE[OF `B \<noteq> G` `G \<noteq> B`]  by  blast
	have "bet B G A" using `bet B G A \<and> seg_eq G A G B` by blast
	have "bet A G B" using betweennesssymmetryE[OF `bet B G A`] .
	obtain C where "bet D H C \<and> seg_eq H C H D" using extensionE[OF `D \<noteq> H` `H \<noteq> D`]  by  blast
	have "bet D H C" using `bet D H C \<and> seg_eq H C H D` by blast
	have "bet C H D" using betweennesssymmetryE[OF `bet D H C`] .
	have "parallel A B C D" using Prop28A[OF `bet A G B` `bet C H D` `bet E G H` `ang_eq E G B G H D` `same_side B D G H`] .
	have "col D H C" using collinear_b `bet D H C \<and> seg_eq H C H D` by blast
	have "col C D H" using collinearorder[OF `col D H C`] by blast
	have "H \<noteq> D" using NCdistinct[OF `\<not> col G H D`] by blast
	have "parallel A B H D" using collinearparallel[OF `parallel A B C D` `col C D H` `H \<noteq> D`] .
	have "parallel H D A B" using parallelsymmetric[OF `parallel A B H D`] .
	have "col B G A" using collinear_b `bet B G A \<and> seg_eq G A G B` by blast
	have "col A B G" using collinearorder[OF `col B G A`] by blast
	have "parallel H D G B" using collinearparallel[OF `parallel H D A B` `col A B G` `G \<noteq> B`] .
	have "parallel G B H D" using parallelsymmetric[OF `parallel H D G B`] .
	thus ?thesis by blast
qed

end