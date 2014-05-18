@model $rootnamespace$.Core.Model.Order
<table class="table table-bordered">
    <tr>
        <th>
            ID
        </th>
        <th>
            Created
        </th>
    </tr>
    <tr>
        <td>@Model.Id
        </td>
        <td>@Model.Created
        </td>
    </tr>
</table>
<h3>
    Order Information</h3>
<table class="table table-bordered">
    <tr>
        <th style="width: 200px">
            Status
        </th>
        <td>
            @Model.OrderStatus
        </td>
    </tr>
    <tr>
        <th>
            Order Total
        </th>
        <td>
            @Model.OrderTotal.ToString("c")
        </td>
    </tr>
</table>
<h3>
    Order Line Items</h3>
<table class="table table-condensed">
    <tr>
        <th>Product Name</th>
        <th>Quantity</th>
        <th>Status</th>
        <th>Total Amount</th>
    </tr>
    @foreach (var item in Model.OrderItems)
    {
        <tr>
            <td>
                @item.Product.Name
            </td>
            <td>
                @item.Quantity
            </td>
            <td>
                @item.OrderStatus
            </td>
            <td>
                @item.TotalPrice.ToString("c")
            </td>
        </tr>
    }
</table>
