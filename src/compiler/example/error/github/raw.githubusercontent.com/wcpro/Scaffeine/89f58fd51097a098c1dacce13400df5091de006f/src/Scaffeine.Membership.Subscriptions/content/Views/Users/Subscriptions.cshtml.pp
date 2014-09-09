@{
    ViewBag.Title = "User Details";
    Layout = "~/Views/Shared/_Folder.cshtml";
}

@using $rootnamespace$.Extensions
@model $rootnamespace$.Models.Users.UserViewModel

<h2>John Doe</h2>


@Html.MvcSiteMap("Modules").Tabs(2,true,false,1)

asdf