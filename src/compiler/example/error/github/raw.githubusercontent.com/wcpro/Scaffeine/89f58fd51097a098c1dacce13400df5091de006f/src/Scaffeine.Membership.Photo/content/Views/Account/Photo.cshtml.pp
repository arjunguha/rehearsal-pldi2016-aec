@model $rootnamespace$.Core.Common.Photos.Photo

@{
    ViewBag.Title = "Photo";
    Layout = "~/Views/Shared/_Folder.cshtml";
    ViewBag.SitemapProvider = "Account";
}

<div class="page-header">
    <h1>
        Your Profile Photo</h1>
</div>
@using (Html.BeginForm("Photo", "Account", FormMethod.Post, new { enctype = "multipart/form-data" }))
{
    <div class="row-fluid">
        <div class="span4">
            <img src="@Url.Content(Model.Url)" alt="" class="img-polaroid"/>
            <input type="file" id="File" name="File" />
        </div>
        <div class="span8">         
            <input type="submit" class="btn" value="Upload Photo" />
        </div>
    </div>
}