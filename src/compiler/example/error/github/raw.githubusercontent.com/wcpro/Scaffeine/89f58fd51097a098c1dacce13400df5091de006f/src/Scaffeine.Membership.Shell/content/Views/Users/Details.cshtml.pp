@{
    ViewBag.Title = "User Details";
    Layout = "_AdminUserLayout.cshtml";
}
@model $rootnamespace$.Models.Users.UserViewModel

<div class="tab-content">
    <div class="tab-pane active" id="details">
        @Html.DisplayForModel("Bootstrap/Bootstrap.Table")
    </div>
</div>