<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

class CreateCustomersTable extends Migration
{
    /**
     * Run the migrations.
     *
     * @return void
     */
    public function up()
    {
        Schema::create('customers', function (Blueprint $table) {
            $table->id('customer_id')->unsigned(); // auto incrementing primary key
            $table->text('first_name');
            $table->text('middle_name')->nullable();
            $table->text('last_name')->nullable();
            $table->tinyText('gender')->nullable();
            $table->date('dob')->nullable();
            $table->text('email');
            $table->string('password', 256);
            $table->text('mobile_no')->nullable();
            $table->text('alternate_mobile')->nullable();
            $table->text('alternate_email')->nullable();
            $table->text('address')->nullable();
            $table->string('city', 256)->nullable();
            $table->string('state', 256)->nullable();
            $table->string('pincode', 50)->nullable();
            $table->text('company')->nullable();
            $table->string('activation_code', 256);
            $table->char('activated', 1)->default('Y')->comment('Y:Yes, N:No');
            $table->string('eia_no', 50)->nullable();
            $table->char('eia_status', 1)->nullable()->comment('0: submitted 1: document verification 2: processing 3: activation 4: eia active');
            $table->string('source', 50)->default('website');
            // $table->timestamp('updated_at')->useCurrent()->nullable()->default(DB::raw('CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP'));
            $table->integer('otp_code')->nullable();
            $table->integer('otp_count')->nullable();
            $table->string('otp_created_date', 50)->nullable();
            $table->string('annual_income', 100)->nullable();
            $table->string('marital_status', 50)->nullable();
            $table->string('country', 256)->nullable();
            $table->integer('document_otp')->nullable();
            $table->string('profile_status', 10)->nullable();

            $table->timestamps();
            
            $table->primary('customer_id');
        });
    }

    /**
     * Reverse the migrations.
     *
     * @return void
     */
    public function down()
    {
        Schema::dropIfExists('customers');
    }
}
