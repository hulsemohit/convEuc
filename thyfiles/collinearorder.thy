theory collinearorder
	imports Geometry collinear1 collinear2
begin

theorem(in euclidean_geometry) collinearorder:
	assumes 
		"col A B C"
	shows "col B A C \<and> col B C A \<and> col C A B \<and> col A C B \<and> col C B A"
proof -
	have "col B C A" using collinear2[OF `col A B C`] .
	have "col C A B" using collinear2[OF `col B C A`] .
	have "col B A C" using collinear1[OF `col A B C`] .
	have "col A C B" using collinear2[OF `col B A C`] .
	have "col C B A" using collinear2[OF `col A C B`] .
	have "col B A C \<and> col B C A \<and> col C A B \<and> col A C B \<and> col C B A" using `col B A C` `col B C A` `col C A B` `col A C B` `col C B A` by blast
	thus ?thesis by blast
qed

end