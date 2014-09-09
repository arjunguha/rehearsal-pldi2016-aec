
@model $rootnamespace$.Photos.Models.Photo

@{
	Layout = null;
}

<!DOCTYPE html>

<html>
	<head>
		<title>title</title>
	</head>
	<body>
		@if(Model != null)
		{
			<span>@Model.Id</span>
			<span>@Model.ResizeName</span>
			<span>@Url.Content(Model.Url)</span>
			<img src="@Url.Content(Model.Url)" alt=""/>
		}
		else {
			<div>
				@using(Html.BeginForm("PhotoUpload", "Photo", FormMethod.Post, new { enctype = "multipart/form-data" }))
				{
					<input type="file" id="File" name="File" />
				
					<input type="submit" value="Upload Photo" />
				}	  
			</div>
		}
	</body>
</html>