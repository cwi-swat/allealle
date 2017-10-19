module translation::Dimensions

import util::Math;
import List; 

data Dimensions
  = square(int arity, int size)
  //| rectangle(list[int] dims, int capacity = int () { throw "please provide a capacity at construction time"; }())  
  ;

@memo
int capacity(square(int arity, int size)) = toInt(pow(size, arity));

Dimensions cross(Dimensions dim1, Dimensions dim2) = square(dim1.arity + dim2.arity, dim1.size) when dim1.size == dim2.size;
default Dimensions cross(Dimensions dim1, Dimensions dim2) { throw "Sizes of both dimensions you cross should be equal (size of the universe)"; }
  
//Dimensions cross(Dimensions dim1, Dimensions dim2) {
//  int n0 = numOfDimensions(dim1);
//  int n1 = numOfDimensions(dim2);
//  
////  if (square(_, int size) := dim1, square(_,size) := dim2) {
//    return square(n0+n1, size);
//  //} else {
//  //  return rectangle([*dimensions(dim1), *dimensions(dim2)], capacity = dim1.capacity*dim2.capacity);    
//  //}   
//}

Dimensions dotJoin(Dimensions dim1, Dimensions dim2) = square(n, dim1.size) when dim1.size == dim2.size, int n := dim1.arity + dim2.arity - 2, n > 0;
default Dimensions dotJoin(Dimensions dim1, Dimensions dim2) { throw "Can not join two unary dimensions"; }

//Dimensions dotJoin(Dimensions dim1, Dimensions dim2) {
//  int n0 = dim1.arity;
//  int n1 = dim2.arity;
//  
//  int n = n0 + n1 - 2;
//  list[int] dims1 = dimensions(dim1);
//  list[int] dims2 = dimensions(dim2);
//  
//  int drop = dims2[0];
//
//  if (n == 0) {
//    throw "Cannot join two unary dimensions";
//  }
//  if (drop != dims1[-1]) {
//    throw "Cannot join two dimensions of different sizes";
//  }
//  
////  if(isSquare(dim1, 0, n0-1) && isSquare(dim2, 1,n1) && (n0 == 1 || n1 == 1 || dims1[0] == dims2[1])) {
//    return square(n, dims1[0]);
//  //} else {
//  //  return rectangle([*[dims1[i] | int i <- [0..n0-1]],*[dims2[i] | int i <- [1..n1]]], capacity = (dim1.capacity*dim2.capacity) / (drop*drop)); 
//  //}
//}

Dimensions transpose(orig:square(int arity, int _)) = orig when arity == 2;
//Dimensions transpose(rectangle(list[int] dims)) = rectangle([dims[1], dims[2]], capacity=capacity) when size(dims) == 2;
default Dimensions transpose(Dimensions _) { throw "Can not transpose a non-binary dimension"; } 

private list[int] dimensions(square(int arity, int size)) = [size | int i <- [0..arity]];
//private list[int] dimensions(rectangle(list[int] dims)) = dims;

//private bool isSquare(square(_,_)) = true;
//private default bool isSquare(Dimensions _) = false;
//
//private bool isSquare(square(int arity,_), int \start, int end) = true when \start>= 0, \start <= end, end <= arity;
//private bool isSquare(rectangle(list[int] dims), int \start, int end) {
//  for (int i <- [\start+1..end]) {
//    if (dims[i-1] != dims[i]) return false;
//  }
//  
//  return true;
//}
//private default bool isSquare(Dimensions _, int _, int _) = false;

//private int numOfDimensions(square(int arity,_)) = arity;
//private int numOfDimensions(rectangle(list[int] dims)) = size(dims); 
