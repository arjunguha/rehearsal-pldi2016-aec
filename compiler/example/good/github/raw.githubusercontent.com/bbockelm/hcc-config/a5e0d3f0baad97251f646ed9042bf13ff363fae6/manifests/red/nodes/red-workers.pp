
node 'node000' inherits red-private {
	$role = "red-worker-el6"
	$condorCustom09 = "el6"
	include general
}


# Older Dell SC1435
node 'node063', 'node064', 'node065', 'node066', 'node067', 'node068', 'node069', 'node070', 'node071', 'node072', 'node073', 'node074', 'node075', 'node076', 'node077', 'node078', 'node079', 'node080', 'node081', 'node082', 'node083', 'node084', 'node085', 'node086', 'node087', 'node088', 'node089', 'node090', 'node091', 'node092', 'node093', 'node094', 'node095', 'node096', 'node097', 'node098', 'node099' inherits red-private {
   $role = "red-worker-el6"
	$condorCustom09 = "el6"
	$isHDFSDatanode = true
	include general
}

# rd13 Dell R710
node 'node103', 'node104', 'node105', 'node106', 'node107', 'node108', 'node109', 'node110' inherits red-private {
	$role = "red-worker-el6"
	$condorCustom09 = "el6"
	$isHDFSDatanode = true
	include general
}

# Sun X2200 M2
node 'red-d19n1', 'red-d19n2', 'red-d19n3','red-d19n4','red-d19n5','red-d19n6','red-d19n7','red-d19n8','red-d19n9','red-d19n10','red-d19n11','red-d19n12','red-d19n13','red-d19n14','red-d19n15','red-d19n16','red-d19n17','red-d19n18','red-d19n19','red-d19n20','red-d19n21','red-d19n22','red-d19n23','red-d19n24','red-d19n25','red-d19n26','red-d19n27','red-d19n28','red-d19n29','red-d19n30','red-d19n31','red-d19n32','red-d19n33','red-d19n34','red-d19n35','red-d19n36','red-d20n1','red-d20n2','red-d20n3','red-d20n4','red-d20n5','red-d20n6','red-d20n7','red-d20n8','red-d20n9','red-d20n10','red-d20n11','red-d20n12','red-d20n13','red-d20n14','red-d20n15','red-d20n16','red-d20n17','red-d20n18','red-d20n19','red-d20n20','red-d20n21','red-d20n22','red-d20n23','red-d20n24','red-d20n25','red-d20n26','red-d20n27','red-d20n28','red-d20n29','red-d20n30','red-d20n31','red-d20n32','red-d20n33','red-d20n34','red-d20n35', 'red-d20n36' inherits red-private {
	$role = "red-worker-el6"
   $condorCustom09 = "el6"
   $isHDFSDatanode = true
   include general
}

# KSU Tier3
node 'node189', 'node190', 'node191', 'node192', 'node193', 'node194', 'node195', 'node196', 'node197', 'node198', 'node199', 'node200' inherits red-private {
	$role = "red-worker-el6"
	$isHDFSDatanode = true
	$condorCustom09 = "el6"
	include general
}

# rd22 Dell R710
node 'node230', 'node231', 'node232', 'node233', 'node234', 'node235', 'node236', 'node237', 'node238', 'node239', 'node240', 'node241', 'node242', 'node243', 'node244', 'node245', 'node246', 'node247', 'node248', 'node249' inherits red-private {
	$role = "red-worker-el6"
	$condorCustom09 = "el6"
	$isHDFSDatanode = true
	include general
}

# Sun X4275
node 'node250', 'node251', 'node252', 'node253', 'node254' inherits red-private {
	$role = "red-worker-el6"
	$isHDFSDatanode = true
	include general
}


# ----------------------------------------------------------------------------


node 'red-d8n1', 'red-d8n3', 'red-d8n4', 'red-d8n5', 'red-d8n6', 'red-d8n7', 'red-d8n8', 'red-d8n9', 'red-d8n10', 'red-d8n11', 'red-d8n12', 'red-d8n13', 'red-d8n14', 'red-d8n15', 'red-d8n16', 'red-d8n17', 'red-d8n18', 'red-d8n19', 'red-d8n20' inherits red-private {
	$role = "red-worker-el6"
   $condorCustom09 = "el6"
   $isHDFSDatanode = true
   include general
}

node 'red-d8n2' inherits red-private {
   $role = "red-worker-el6"
   $condorCustom09 = "red-d8n2"
   $isHDFSDatanode = true
   include general
}

node 'red-d9n1', 'red-d9n2', 'red-d9n3', 'red-d9n4', 'red-d9n5', 'red-d9n6', 'red-d9n7', 'red-d9n8', 'red-d9n9', 'red-d9n10', 'red-d9n11', 'red-d9n12', 'red-d9n13', 'red-d9n14', 'red-d9n15', 'red-d9n16', 'red-d9n17', 'red-d9n18', 'red-d9n19', 'red-d9n20' inherits red-private {
	$role = "red-worker-el6"
	$condorCustom09="el6"
	$isHDFSDatanode = true
	include general
}

node 'red-d11n1', 'red-d11n2', 'red-d11n3', 'red-d11n4', 'red-d11n5', 'red-d11n6', 'red-d11n7', 'red-d11n8', 'red-d11n9', 'red-d11n10', 'red-d11n11', 'red-d11n12', 'red-d11n13', 'red-d11n14', 'red-d11n15', 'red-d11n16', 'red-d11n17', 'red-d11n18', 'red-d11n19', 'red-d11n20' inherits red-private {
	$role = "red-worker-el6"
	$condorCustom09 = "el6"
	$isHDFSDatanode = true
	include general
}

node 'red-d15n1', 'red-d15n2', 'red-d15n3', 'red-d15n4', 'red-d15n5', 'red-d15n6', 'red-d15n7', 'red-d15n8', 'red-d15n9', 'red-d15n10', 'red-d15n11', 'red-d15n12', 'red-d15n13', 'red-d15n14', 'red-d15n15', 'red-d15n16', 'red-d15n17', 'red-d15n18' , 'red-d15n19', 'red-d15n20', 'red-d15n21', 'red-d15n22', 'red-d15n23', 'red-d15n24', 'red-d15n25', 'red-d15n26' inherits red-private {
	$role = "red-worker-el6"
   $condorCustom09 = "el6"
   $isHDFSDatanode = true
   include general
}

node 'red-d16n1', 'red-d16n2', 'red-d16n3', 'red-d16n4', 'red-d16n5', 'red-d16n6', 'red-d16n7', 'red-d16n8', 'red-d16n9', 'red-d16n10', 'red-d16n11', 'red-d16n12', 'red-d16n13', 'red-d16n14', 'red-d16n15', 'red-d16n16', 'red-d16n17', 'red-d16n18', 'red-d16n19', 'red-d16n20', 'red-d16n21', 'red-d16n22', 'red-d16n23', 'red-d16n24', 'red-d16n25', 'red-d16n26'  inherits red-private {
	$role = "red-worker-el6"
   $condorCustom09 = "el6"
   $isHDFSDatanode = true
   include general
}

#node 'red-d18n1', 'red-d18n2', 'red-d18n3', 'red-d18n4', 'red-d18n5', 'red-d18n6', 'red-d18n7', 'red-d18n8', 'red-d18n9', 'red-d18n10', 'red-d18n11', 'red-d18n12', 'red-d18n13', 'red-d18n14', 'red-d18n15', 'red-d18n16', 'red-d18n17', 'red-d18n18', 'red-d18n19', 'red-d18n20', 'red-d18n21', 'red-d18n22', 'red-d18n23', 'red-d18n24', 'red-d18n25', 'red-d18n26', 'red-d18n27', 'red-d18n28', 'red-d18n29', 'red-d18n30', 'red-d18n31', 'red-d18n32', 'red-d18n33', 'red-d18n34', 'red-d18n35', 'red-d18n36' inherits red-private {
node 'red-d18n1', 'red-d18n3', 'red-d18n4', 'red-d18n5', 'red-d18n6', 'red-d18n7', 'red-d18n8', 'red-d18n9', 'red-d18n10', 'red-d18n11', 'red-d18n12', 'red-d18n13', 'red-d18n14', 'red-d18n15', 'red-d18n16', 'red-d18n17', 'red-d18n18', 'red-d18n19', 'red-d18n20', 'red-d18n21', 'red-d18n22', 'red-d18n23', 'red-d18n24', 'red-d18n25', 'red-d18n26', 'red-d18n27', 'red-d18n28', 'red-d18n29', 'red-d18n30', 'red-d18n31', 'red-d18n32', 'red-d18n33', 'red-d18n34', 'red-d18n35', 'red-d18n36' inherits red-private {
	$role = "red-worker-el6"
   $condorCustom09 = "el6"
   $isHDFSDatanode = true
   include general
}


#--- 720xds ---#

node 'red-d21n1', 'red-d21n2', 'red-d21n3', 'red-d21n4', 'red-d21n5', 'red-d21n6', 'red-d21n7', 'red-d21n8', 'red-d21n9', 'red-d21n10', 'red-d21n11', 'red-d21n12', 'red-d21n13', 'red-d21n14', 'red-d21n15', 'red-d21n16' inherits red-private {
	$role = "red-worker-el6"
   $condorCustom09 = "el6"
   $isHDFSDatanode = true
   include general
}

node 'red-d22n1', 'red-d22n2', 'red-d22n3', 'red-d22n4', 'red-d22n5', 'red-d22n6', 'red-d22n7', 'red-d22n8', 'red-d22n9', 'red-d22n10', 'red-d22n11', 'red-d22n12', 'red-d22n13', 'red-d22n14', 'red-d22n15', 'red-d22n16' inherits red-private {
	$role = "red-worker-el6"
   $condorCustom09 = "el6"
   $isHDFSDatanode = true
   include general
}
node 'red-d23n1', 'red-d23n2', 'red-d23n3', 'red-d23n4', 'red-d23n5', 'red-d23n6', 'red-d23n7', 'red-d23n8', 'red-d23n9', 'red-d23n10', 'red-d23n11', 'red-d23n12', 'red-d23n13', 'red-d23n14', 'red-d23n15', 'red-d23n16' inherits red-private {
	$role = "red-worker-el6"
   $condorCustom09 = "el6"
   $isHDFSDatanode = true
   include general
}
