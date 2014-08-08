@{
    Layout = "~/Views/Shared/_Folder.cshtml";
}

@using $rootnamespace$.Extensions
@model $rootnamespace$.Models.Users.UserViewModel

<div class="page-header">
    <h3>@Model.FullName</h3>
</div>

<div class="btn-group pull-right">
    <a class="btn btn-inverse dropdown-toggle" data-toggle="dropdown" href="#">Action
    <span class="caret"></span>
    </a>
    <ul class="dropdown-menu">
        @if (Model.IsLockedOut)
        {
            <li><a href="#" id="lock-user"><i class="icon-lock"></i>Lock User</a></li>
        }
        else
        {
            <li><a href="#" id="unlock-user"><i class="icon-unlock"></i>Unlock User</a></li>
        }
    </ul>
</div>
@Html.MvcSiteMap("Modules").Tabs(2, true, false, 1)

@RenderBody()