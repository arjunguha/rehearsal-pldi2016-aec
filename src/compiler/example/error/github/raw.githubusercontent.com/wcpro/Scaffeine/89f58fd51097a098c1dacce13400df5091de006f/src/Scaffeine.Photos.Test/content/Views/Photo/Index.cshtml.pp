@model List<$rootnamespace$.Photos.Models.Photo>

@{
	Layout = null;
}

<!DOCTYPE html>

<html>
	<head>
		<title>Photos</title>
	</head>
	<body>
		<div>
			<ul>
			@foreach(var p in Model)
			{
				<li style="list-style-type: decimal">
					<div>ID: @p.Id</div> 
					<div>Size Type: @p.ResizeName</div> 
					<div><img src="@Url.Content(p.Url)" alt="" /></div> 
				</li>
			}  
			</ul>
		</div>
	</body>
</html>