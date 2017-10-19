module translation::tests::DimensionsTest

import translation::Dimensions;

import IO;
import List;

test bool theCrossProductOfTwoSquaresIsAlsoSquare(int ar1, int s1, int ar2, int s2) {
  Dimensions d1 = square(ar1, s1);
  Dimensions d2 = square(ar2, s2);
  
  if (s1 == s2, square(int newAr, size) !:= cross(d1,d2), newAr != ar1+ar2) {
      fail;
  }
  
  return true;
}
